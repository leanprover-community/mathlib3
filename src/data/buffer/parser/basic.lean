/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.string.basic
import data.buffer.basic
import data.nat.digits

/-!
# Parsers

`parser α` is the type that describes a computation that can ingest a `char_buffer`
and output, if successful, a term of type `α`.
This file expands on the definitions in the core library, proving that all the core library
parsers are `mono`. There are also lemmas on the composability of parsers.

## Main definitions

* `parse_result.pos` : The position of a `char_buffer` at which a `parser α` has finished.
* `parser.mono` : The property that a parser only moves forward within a buffer,
  in both cases of success or failure.

## Implementation details

Lemmas about how parsers are mono are in the `mono` namespace. That allows using projection
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
A `p : parser α` is defined to be `mono` if the result `p cb n` it gives,
for some `cb : char_buffer` and `n : ℕ`, (whether `done` or `fail`),
is always at a `parse_result.pos` that is at least `n`.
The `mono` property is used mainly for proper `orelse` behavior.
-/
class mono : Prop :=
(le' : ∀ (cb : char_buffer) (n : ℕ), n ≤ (p cb n).pos)

lemma mono.le [p.mono] : n ≤ (p cb n).pos := mono.le' cb n

/--
A `parser α` is defined to be `static` if it does not move on success.
-/
class static : Prop :=
(of_done : ∀ {cb : char_buffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n = n')

/--
A `parser α` is defined to be `err_static` if it does not move on error.
-/
class err_static : Prop :=
(of_fail : ∀ {cb : char_buffer} {n n' : ℕ} {err : dlist string}, p cb n = fail n' err → n = n')

/--
A `parser α` is defined to be `step` if it always moves exactly one char forward on success.
-/
class step : Prop :=
(of_done : ∀ {cb : char_buffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n' = n + 1)

/--
A `parser α` is defined to be `prog` if it always moves forward on success.
-/
class prog : Prop :=
(of_done : ∀ {cb : char_buffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n < n')

/--
A `parser a` is defined to be `bounded` if it produces a
`fail` `parse_result` when it is parsing outside the provided `char_buffer`.
-/
class bounded : Prop :=
(ex' : ∀ {cb : char_buffer} {n : ℕ}, cb.size ≤ n → ∃ (n' : ℕ) (err : dlist string),
  p cb n = fail n' err)

lemma bounded.exists (p : parser α) [p.bounded] {cb : char_buffer} {n : ℕ} (h : cb.size ≤ n) :
  ∃ (n' : ℕ) (err : dlist string), p cb n = fail n' err :=
bounded.ex' h

/--
A `parser a` is defined to be `unfailing` if it always produces a `done` `parse_result`.
-/
class unfailing : Prop :=
(ex' : ∀ (cb : char_buffer) (n : ℕ), ∃ (n' : ℕ) (a : α), p cb n = done n' a)

/--
A `parser a` is defined to be `conditionally_unfailing` if it produces a
`done` `parse_result` as long as it is parsing within the provided `char_buffer`.
-/
class conditionally_unfailing : Prop :=
(ex' : ∀ {cb : char_buffer} {n : ℕ}, n < cb.size → ∃ (n' : ℕ) (a : α), p cb n = done n' a)

lemma fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔
    ∃ (pos' : ℕ) (err : dlist string), p cb n = fail pos' err :=
by cases p cb n; simp

lemma success_iff :
  (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
by cases p cb n; simp

variables {p q cb n n' msgs msg}

lemma mono.of_done [p.mono] (h : p cb n = done n' a) : n ≤ n' :=
by simpa [h] using mono.le p cb n

lemma mono.of_fail [p.mono] (h : p cb n = fail n' err) : n ≤ n' :=
by simpa [h] using mono.le p cb n

lemma bounded.of_done [p.bounded] (h : p cb n = done n' a) : n < cb.size :=
begin
  contrapose! h,
  obtain ⟨np, err, hp⟩ := bounded.exists p h,
  simp [hp]
end

lemma static.iff :
  static p ↔ (∀ (cb : char_buffer) (n n' : ℕ) (a : α), p cb n = done n' a → n = n') :=
⟨λ h _ _ _ _ hp, by { haveI := h, exact static.of_done hp}, λ h, ⟨h⟩⟩

lemma exists_done (p : parser α) [p.unfailing] (cb : char_buffer) (n : ℕ) :
  ∃ (n' : ℕ) (a : α), p cb n = done n' a :=
unfailing.ex' cb n

lemma unfailing.of_fail [p.unfailing] (h : p cb n = fail n' err) : false :=
begin
  obtain ⟨np, a, hp⟩ := p.exists_done cb n,
  simpa [hp] using h
end

@[priority 100] -- see Note [lower instance priority]
instance conditionally_unfailing_of_unfailing [p.unfailing] : conditionally_unfailing p :=
⟨λ _ _ _, p.exists_done _ _⟩

lemma exists_done_in_bounds (p : parser α) [p.conditionally_unfailing] {cb : char_buffer} {n : ℕ}
  (h : n < cb.size) : ∃ (n' : ℕ) (a : α), p cb n = done n' a :=
conditionally_unfailing.ex' h

lemma conditionally_unfailing.of_fail [p.conditionally_unfailing] (h : p cb n = fail n' err)
  (hn : n < cb.size) : false :=
begin
  obtain ⟨np, a, hp⟩ := p.exists_done_in_bounds hn,
  simpa [hp] using h
end

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
  @decorate_errors α msgs p cb n = fail n' err ↔
    n = n' ∧ err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
by cases h : p cb n; simp [decorate_errors, h, eq_comm]

@[simp] lemma decorate_error_eq_fail :
  @decorate_error α msg p cb n = fail n' err ↔
    n = n' ∧ err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
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

lemma orelse_eq_fail_not_mono_lt (hn : n' < n) : (p <|> q) cb n = fail n' err ↔
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

lemma orelse_eq_fail_of_mono_ne [q.mono] (hn : n ≠ n') :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases h : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, h, hn, hq, hn, ←orelse_eq_orelse, parser.orelse] },
      { have : n ≤ nq := mono.of_fail hq,
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

lemma guard_eq_done {p : Prop} [decidable p] {u : unit} :
  @guard parser _ p _ cb n = done n' u ↔ p ∧ n = n' :=
by { by_cases hp : p; simp [guard, hp, pure_eq_done] }

lemma guard_eq_fail {p : Prop} [decidable p] :
  @guard parser _ p _ cb n = fail n' err ↔ (¬ p) ∧ n = n' ∧ err = dlist.empty :=
by { by_cases hp : p; simp [guard, hp, eq_comm, pure_eq_done] }

namespace mono

variables {sep : parser unit}

instance pure : mono (pure a) :=
⟨λ _ _, by simp [pure_eq_done]⟩

instance bind {f : α → parser β} [p.mono] [∀ a, (f a).mono] :
  (p >>= f).mono :=
begin
  constructor,
  intros cb n,
  cases hx : (p >>= f) cb n,
  { obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx,
    refine le_trans (of_done h) _,
    simpa [h'] using of_done h' },
  { obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx,
    { simpa [h] using of_fail h },
    { refine le_trans (of_done h) _,
      simpa [h'] using of_fail h' } }
end

instance and_then {q : parser β} [p.mono] [q.mono] : (p >> q).mono := mono.bind

instance map [p.mono] {f : α → β} : (f <$> p).mono := mono.bind

instance seq {f : parser (α → β)} [f.mono] [p.mono] : (f <*> p).mono := mono.bind

instance mmap : Π {l : list α} {f : α → parser β} [∀ a ∈ l, (f a).mono],
  (l.mmap f).mono
| []       _ _ := mono.pure
| (a :: l) f h := begin
  convert mono.bind,
  { exact h _ (list.mem_cons_self _ _) },
  { intro,
    convert mono.map,
    convert mmap,
    exact (λ _ ha, h _ (list.mem_cons_of_mem _ ha)) }
end

instance mmap' : Π {l : list α} {f : α → parser β} [∀ a ∈ l, (f a).mono],
  (l.mmap' f).mono
| []       _ _ := mono.pure
| (a :: l) f h := begin
  convert mono.and_then,
  { exact h _ (list.mem_cons_self _ _) },
  { convert mmap',
    exact (λ _ ha, h _ (list.mem_cons_of_mem _ ha)) }
end

instance failure : (failure : parser α).mono :=
⟨by simp [le_refl]⟩

instance guard {p : Prop} [decidable p] : mono (guard p) :=
⟨by { by_cases h : p; simp [h, pure_eq_done, le_refl] }⟩

instance orelse [p.mono] [q.mono] : (p <|> q).mono :=
begin
  constructor,
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx;
    simpa [h] using of_done h },
  { by_cases h : n = posx,
    { simp [hx, h] },
    { simp only [orelse_eq_fail_of_mono_ne h] at hx,
      exact of_fail hx } }
end

instance decorate_errors [p.mono] :
  (@decorate_errors α msgs p).mono :=
begin
  constructor,
  intros cb n,
  cases h : p cb n,
  { simpa [decorate_errors, h] using of_done h },
  { simp [decorate_errors, h] }
end

instance decorate_error [p.mono] : (@decorate_error α msg p).mono :=
mono.decorate_errors

instance any_char : mono any_char :=
begin
  constructor,
  intros cb n,
  by_cases h : n < cb.size;
  simp [any_char, h],
end

instance sat {p : char → Prop} [decidable_pred p] : mono (sat p) :=
begin
  constructor,
  intros cb n,
  simp only [sat],
  split_ifs;
  simp
end

instance eps : mono eps := mono.pure

instance ch {c : char} : mono (ch c) := mono.decorate_error

instance char_buf {s : char_buffer} : mono (char_buf s) :=
mono.decorate_error

instance one_of {cs : list char} : (one_of cs).mono :=
mono.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).mono :=
mono.and_then

instance str {s : string} : (str s).mono :=
mono.decorate_error

instance remaining : remaining.mono :=
⟨λ _ _, le_refl _⟩

instance eof : eof.mono :=
mono.decorate_error

instance foldr_core {f : α → β → β} {b : β} [p.mono] :
  ∀ {reps : ℕ}, (foldr_core f p b reps).mono
| 0          := mono.failure
| (reps + 1) := begin
  convert mono.orelse,
  { convert mono.bind,
    { apply_instance },
    { exact λ _, @mono.bind _ _ _ _ foldr_core _ } },
  { exact mono.pure }
end

instance foldr {f : α → β → β} [p.mono] : mono (foldr f p b) :=
⟨λ _ _, by { convert mono.le (foldr_core f p b _) _ _, exact mono.foldr_core }⟩

instance foldl_core {f : α → β → α} {p : parser β} [p.mono] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).mono
| _ 0          := mono.failure
| _ (reps + 1) := begin
  convert mono.orelse,
  { convert mono.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact mono.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.mono] : mono (foldl f a p) :=
⟨λ _ _, by { convert mono.le (foldl_core f a p _) _ _, exact mono.foldl_core }⟩

instance many [p.mono] : p.many.mono :=
mono.foldr

instance many_char {p : parser char} [p.mono] : p.many_char.mono :=
mono.map

instance many' [p.mono] : p.many'.mono :=
mono.and_then

instance many1 [p.mono] : p.many1.mono :=
mono.seq

instance many_char1 {p : parser char} [p.mono] : p.many_char1.mono :=
mono.map

instance sep_by1 [p.mono] [sep.mono] : mono (sep_by1 sep p) :=
mono.seq

instance sep_by [p.mono] [hs : sep.mono] : mono (sep_by sep p) :=
mono.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.mono → (F p).mono) :
  ∀ (max_depth : ℕ), mono (fix_core F max_depth)
| 0               := mono.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.mono :=
mono.decorate_error

instance nat : nat.mono :=
mono.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.mono → (F p).mono) :
  mono (fix F) :=
⟨λ _ _, by { convert mono.le (parser.fix_core F _) _ _, exact fix_core hF _ }⟩

end mono

@[simp] lemma orelse_pure_eq_fail : (p <|> pure a) cb n = fail n' err ↔
  p cb n = fail n' err ∧ n ≠ n' :=
begin
  by_cases hn : n = n',
  { simp [hn, pure_eq_done] },
  { simp [orelse_eq_fail_of_mono_ne, hn] }
end

end defn_lemmas

section done

variables {α β : Type} {cb : char_buffer} {n n' : ℕ} {a a' : α} {b : β} {c : char} {u : unit}
  {err : dlist string}

lemma any_char_eq_done : any_char cb n = done n' c ↔
  ∃ (hn : n < cb.size), n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
begin
  simp_rw [any_char],
  split_ifs with h;
  simp [h, eq_comm]
end

lemma any_char_eq_fail : any_char cb n = fail n' err ↔ n = n' ∧ err = dlist.empty ∧ cb.size ≤ n :=
begin
  simp_rw [any_char],
  split_ifs with h;
  simp [←not_lt, h, eq_comm]
end

lemma sat_eq_done {p : char → Prop} [decidable_pred p] : sat p cb n = done n' c ↔
  ∃ (hn : n < cb.size), p c ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
begin
  by_cases hn : n < cb.size,
  { by_cases hp : p (cb.read ⟨n, hn⟩),
    { simp only [sat, hn, hp, dif_pos, if_true, exists_prop_of_true],
      split,
      { rintro ⟨rfl, rfl⟩, simp [hp] },
      { rintro ⟨-, rfl, rfl⟩, simp } },
    { simp only [sat, hn, hp, dif_pos, false_iff, not_and, exists_prop_of_true, if_false],
      rintro H - rfl,
      exact hp H } },
  { simp [sat, hn] }
end

lemma sat_eq_fail {p : char → Prop} [decidable_pred p] : sat p cb n = fail n' err ↔
  n = n' ∧ err = dlist.empty ∧ ∀ (h : n < cb.size), ¬ p (cb.read ⟨n, h⟩) :=
begin
  dsimp only [sat],
  split_ifs;
  simp [*, eq_comm]
end

lemma eps_eq_done : eps cb n = done n' u ↔ n = n' := by simp [eps, pure_eq_done]

lemma ch_eq_done : ch c cb n = done n' u ↔ ∃ (hn : n < cb.size), n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [ch, eps_eq_done, sat_eq_done, and.comm, @eq_comm _ n']

lemma char_buf_eq_done {cb' : char_buffer} : char_buf cb' cb n = done n' u ↔
  n + cb'.size = n' ∧ cb'.to_list <+: (cb.to_list.drop n) :=
begin
  simp only [char_buf, decorate_error_eq_done, ne.def, ←buffer.length_to_list],
  induction cb'.to_list with hd tl hl generalizing cb n n',
  { simp [pure_eq_done, mmap'_eq_done, -buffer.length_to_list, list.nil_prefix] },
  { simp only [ch_eq_done, and.comm, and.assoc, and.left_comm, hl, mmap', and_then_eq_bind,
               bind_eq_done, list.length, exists_and_distrib_left, exists_const],
    split,
    { rintro ⟨np, h, rfl, rfl, hn, rfl⟩,
      simp only [add_comm, add_left_comm, h, true_and, eq_self_iff_true, and_true],
      have : n < cb.to_list.length := by simpa using hn,
      rwa [←buffer.nth_le_to_list _ this, ←list.cons_nth_le_drop_succ this, list.prefix_cons_inj] },
    { rintro ⟨h, rfl⟩,
      by_cases hn : n < cb.size,
      { have : n < cb.to_list.length := by simpa using hn,
        rw [←list.cons_nth_le_drop_succ this, list.cons_prefix_iff] at h,
        use [n + 1, h.right],
        simpa [buffer.nth_le_to_list, add_comm, add_left_comm, add_assoc, hn] using h.left.symm },
      { have : cb.to_list.length ≤ n := by simpa using hn,
        rw list.drop_eq_nil_of_le this at h,
        simpa using h } } }
end

lemma one_of_eq_done {cs : list char} : one_of cs cb n = done n' c ↔
  ∃ (hn : n < cb.size), c ∈ cs ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [one_of, sat_eq_done]

lemma one_of'_eq_done {cs : list char} : one_of' cs cb n = done n' u ↔
  ∃ (hn : n < cb.size), cb.read ⟨n, hn⟩ ∈ cs ∧ n' = n + 1 :=
begin
  simp only [one_of', one_of_eq_done, eps_eq_done, and.comm, and_then_eq_bind, bind_eq_done,
             exists_eq_left, exists_and_distrib_left],
  split,
  { rintro ⟨c, hc, rfl, hn, rfl⟩,
    exact ⟨rfl, hn, hc⟩ },
  { rintro ⟨rfl, hn, hc⟩,
    exact ⟨cb.read ⟨n, hn⟩, hc, rfl, hn, rfl⟩ }
end

lemma str_eq_char_buf (s : string) : str s = char_buf s.to_list.to_buffer :=
begin
  ext cb n,
  rw [str, char_buf],
  congr,
  { simp [buffer.to_string, string.as_string_inv_to_list] },
  { simp }
end

lemma str_eq_done {s : string} : str s cb n = done n' u ↔
  n + s.length = n' ∧ s.to_list <+: (cb.to_list.drop n) :=
by simp [str_eq_char_buf, char_buf_eq_done]

lemma remaining_eq_done {r : ℕ} : remaining cb n = done n' r ↔ n = n' ∧ cb.size - n = r :=
by simp [remaining]

lemma remaining_ne_fail : remaining cb n ≠ fail n' err :=
by simp [remaining]

lemma eof_eq_done {u : unit} : eof cb n = done n' u ↔ n = n' ∧ cb.size ≤ n :=
by simp [eof, guard_eq_done, remaining_eq_done, tsub_eq_zero_iff_le, and_comm, and_assoc]

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

lemma foldr_eq_fail_iff_mono_at_end {f : α → β → β} {p : parser α} {err : dlist string}
  [p.mono] (hc : cb.size ≤ n) : foldr f p b cb n = fail n' err ↔
    n < n' ∧ (p cb n = fail n' err ∨ ∃ (a : α), p cb n = done n' a ∧ err = dlist.empty) :=
begin
  have : cb.size - n = 0 := tsub_eq_zero_iff_le.mpr hc,
  simp only [foldr, foldr_core_succ_eq_fail, this, and.left_comm, foldr_core_zero_eq_fail,
             ne_iff_lt_iff_le, exists_and_distrib_right, exists_eq_left, and.congr_left_iff,
             exists_and_distrib_left],
  rintro (h | ⟨⟨a, h⟩, rfl⟩),
  { exact mono.of_fail h },
  { exact mono.of_done h }
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
by simp [foldl_core, and_comm]

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

lemma foldl_eq_fail_iff_mono_at_end {f : β → α → β} {p : parser α} {err : dlist string}
  [p.mono] (hc : cb.size ≤ n) : foldl f b p cb n = fail n' err ↔
    n < n' ∧ (p cb n = fail n' err ∨ ∃ (a : α), p cb n = done n' a ∧ err = dlist.empty) :=
begin
  have : cb.size - n = 0 := tsub_eq_zero_iff_le.mpr hc,
  simp only [foldl, foldl_core_succ_eq_fail, this, and.left_comm, ne_iff_lt_iff_le, exists_eq_left,
             exists_and_distrib_right, and.congr_left_iff, exists_and_distrib_left,
             foldl_core_zero_eq_fail],
  rintro (h | ⟨⟨a, h⟩, rfl⟩),
  { exact mono.of_fail h },
  { exact mono.of_done h }
end

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

lemma many'_eq_done {p : parser α} : many' p cb n = done n' u ↔
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

lemma digit_eq_done {k : ℕ} : digit cb n = done n' k ↔ ∃ (hn : n < cb.size), n' = n + 1 ∧ k ≤ 9 ∧
  (cb.read ⟨n, hn⟩).to_nat - '0'.to_nat = k ∧ '0' ≤ cb.read ⟨n, hn⟩ ∧ cb.read ⟨n, hn⟩ ≤ '9' :=
begin
  have c9 : '9'.to_nat - '0'.to_nat = 9 := rfl,
  have l09 : '0'.to_nat ≤ '9'.to_nat := dec_trivial,
  have le_iff_le : ∀ {c c' : char}, c ≤ c' ↔ c.to_nat ≤ c'.to_nat := λ _ _, iff.rfl,
  split,
  { simp only [digit, sat_eq_done, pure_eq_done, decorate_error_eq_done, bind_eq_done, ←c9],
    rintro ⟨np, c, ⟨hn, ⟨ge0, le9⟩, rfl, rfl⟩, rfl, rfl⟩,
    simpa [hn, ge0, le9, true_and, and_true, eq_self_iff_true, exists_prop_of_true,
            tsub_le_tsub_iff_right, l09] using (le_iff_le.mp le9) },
  { simp only [digit, sat_eq_done, pure_eq_done, decorate_error_eq_done, bind_eq_done, ←c9,
               le_iff_le],
    rintro ⟨hn, rfl, -, rfl, ge0, le9⟩,
    use [n + 1, cb.read ⟨n, hn⟩],
    simp [hn, ge0, le9] }
end

lemma digit_eq_fail : digit cb n = fail n' err ↔ n = n' ∧ err = dlist.of_list ["<digit>"] ∧
  ∀ (h : n < cb.size), ¬ ((λ c, '0' ≤ c ∧ c ≤ '9') (cb.read ⟨n, h⟩)) :=
by simp [digit, sat_eq_fail]


end done

namespace static

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma not_of_ne (h : p cb n = done n' a) (hne : n ≠ n') : ¬ static p :=
by { introI, exact hne (of_done h) }

instance pure : static (pure a) :=
⟨λ _ _ _ _, by { simp_rw pure_eq_done, rw [and.comm], simp }⟩

instance bind {f : α → parser β} [p.static] [∀ a, (f a).static] :
  (p >>= f).static :=
⟨λ _ _ _ _, by { rw bind_eq_done, rintro ⟨_, _, hp, hf⟩, exact trans (of_done hp) (of_done hf) }⟩

instance and_then {q : parser β} [p.static] [q.static] : (p >> q).static := static.bind

instance map [p.static] {f : α → β} : (f <$> p).static :=
⟨λ _ _ _ _, by { simp_rw map_eq_done, rintro ⟨_, hp, _⟩, exact of_done hp }⟩

instance seq {f : parser (α → β)} [f.static] [p.static] : (f <*> p).static := static.bind

instance mmap : Π {l : list α} {f : α → parser β} [∀ a, (f a).static], (l.mmap f).static
| []       _ _ := static.pure
| (a :: l) _ h := begin
  convert static.bind,
  { exact h _ },
  { intro,
    convert static.bind,
    { convert mmap,
      exact h },
    { exact λ _, static.pure } }
end

instance mmap' : Π {l : list α} {f : α → parser β} [∀ a, (f a).static], (l.mmap' f).static
| []       _ _ := static.pure
| (a :: l) _ h := begin
  convert static.and_then,
  { exact h _ },
  { convert mmap',
    exact h }
end

instance failure : @parser.static α failure :=
⟨λ _ _ _ _, by simp⟩

instance guard {p : Prop} [decidable p] : static (guard p) :=
⟨λ _ _ _ _, by simp [guard_eq_done]⟩

instance orelse [p.static] [q.static] : (p <|> q).static :=
⟨λ _ _ _ _, by { simp_rw orelse_eq_done, rintro (h | ⟨h, -⟩); exact of_done h }⟩

instance decorate_errors [p.static] :
  (@decorate_errors α msgs p).static :=
⟨λ _ _ _ _, by { rw decorate_errors_eq_done, exact of_done }⟩

instance decorate_error [p.static] : (@decorate_error α msg p).static :=
static.decorate_errors

lemma any_char : ¬ static any_char :=
begin
  have : any_char "s".to_char_buffer 0 = done 1 's',
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [any_char_eq_done, this] },
  exact not_of_ne this zero_ne_one
end

lemma sat_iff {p : char → Prop} [decidable_pred p] : static (sat p) ↔ ∀ c, ¬ p c :=
begin
  split,
  { introI,
    intros c hc,
    have : sat p [c].to_buffer 0 = done 1 c := by simp [sat_eq_done, hc],
    exact zero_ne_one (of_done this) },
  { contrapose!,
    simp only [iff, sat_eq_done, and_imp, exists_prop, exists_and_distrib_right,
               exists_and_distrib_left, exists_imp_distrib, not_forall],
    rintros _ _ _ a h hne rfl hp -,
    exact ⟨a, hp⟩ }
end

instance sat : static (sat (λ _, false)) :=
by { apply sat_iff.mpr, simp }

instance eps : static eps := static.pure

lemma ch (c : char) : ¬ static (ch c) :=
begin
  have : ch c [c].to_buffer 0 = done 1 (),
    { have : 0 < [c].to_buffer.size := dec_trivial,
      simp [ch_eq_done, this] },
  exact not_of_ne this zero_ne_one
end

lemma char_buf_iff {cb' : char_buffer} : static (char_buf cb') ↔ cb' = buffer.nil :=
begin
  rw ←buffer.size_eq_zero_iff,
  have : char_buf cb' cb' 0 = done cb'.size () := by simp [char_buf_eq_done],
  cases hc : cb'.size with n,
  { simp only [eq_self_iff_true, iff_true],
    exact ⟨λ _ _ _ _ h, by simpa [hc] using (char_buf_eq_done.mp h).left⟩ },
  { rw hc at this,
    simpa [nat.succ_ne_zero] using not_of_ne this (nat.succ_ne_zero n).symm }
end

lemma one_of_iff {cs : list char} : static (one_of cs) ↔ cs = [] :=
begin
  cases cs with hd tl,
  { simp [one_of, static.decorate_errors] },
  { have : one_of (hd :: tl) (hd :: tl).to_buffer 0 = done 1 hd,
      { simp [one_of_eq_done] },
    simpa using not_of_ne this zero_ne_one }
end

instance one_of : static (one_of []) :=
by { apply one_of_iff.mpr, refl }

lemma one_of'_iff {cs : list char} : static (one_of' cs) ↔ cs = [] :=
begin
  cases cs with hd tl,
  { simp [one_of', static.bind], },
  { have : one_of' (hd :: tl) (hd :: tl).to_buffer 0 = done 1 (),
      { simp [one_of'_eq_done] },
    simpa using not_of_ne this zero_ne_one }
end

instance one_of' : static (one_of []) :=
by { apply one_of_iff.mpr, refl }

lemma str_iff {s : string} : static (str s) ↔ s = "" :=
by simp [str_eq_char_buf, char_buf_iff, ←string.to_list_inj, buffer.ext_iff]

instance remaining : remaining.static :=
⟨λ _ _ _ _ h, (remaining_eq_done.mp h).left⟩

instance eof : eof.static :=
static.decorate_error

instance foldr_core {f : α → β → β} [p.static] :
  ∀ {b : β} {reps : ℕ}, (foldr_core f p b reps).static
| _ 0          := static.failure
| _ (reps + 1) := begin
  simp_rw parser.foldr_core,
  convert static.orelse,
  { convert static.bind,
    { apply_instance },
    { intro,
      convert static.bind,
      { exact foldr_core },
      { apply_instance } } },
  { exact static.pure }
end

instance foldr {f : α → β → β} [p.static] : static (foldr f p b) :=
⟨λ _ _ _ _, by { dsimp [foldr], exact of_done }⟩

instance foldl_core {f : α → β → α} {p : parser β} [p.static] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).static
| _ 0          := static.failure
| _ (reps + 1) := begin
  convert static.orelse,
  { convert static.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact static.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.static] : static (foldl f a p) :=
⟨λ _ _ _ _, by { dsimp [foldl], exact of_done }⟩

instance many [p.static] : p.many.static :=
static.foldr

instance many_char {p : parser char} [p.static] : p.many_char.static :=
static.map

instance many' [p.static] : p.many'.static :=
static.and_then

instance many1 [p.static] : p.many1.static :=
static.seq

instance many_char1 {p : parser char} [p.static] : p.many_char1.static :=
static.map

instance sep_by1 [p.static] [sep.static] : static (sep_by1 sep p) :=
static.seq

instance sep_by [p.static] [sep.static] : static (sep_by sep p) :=
static.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.static → (F p).static) :
  ∀ (max_depth : ℕ), static (fix_core F max_depth)
| 0               := static.failure
| (max_depth + 1) := hF _ (fix_core _)

lemma digit : ¬ digit.static :=
begin
  have : digit "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma nat : ¬ nat.static :=
begin
  have : nat "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.static → (F p).static) :
  static (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact static.of_done h }⟩

end static

namespace bounded

variables {α β : Type} {msgs : thunk (list string)} {msg : thunk string}
variables {p q : parser α} {cb : char_buffer} {n n' : ℕ} {err : dlist string}
variables {a : α} {b : β}

lemma done_of_unbounded (h : ¬p.bounded) : ∃ (cb : char_buffer) (n n' : ℕ) (a : α),
  p cb n = done n' a ∧ cb.size ≤ n :=
begin
  contrapose! h,
  constructor,
  intros cb n hn,
  cases hp : p cb n,
  { exact absurd hn (h _ _ _ _ hp).not_le },
  { simp [hp] }
end

lemma pure : ¬ bounded (pure a) :=
begin
  introI,
  have : (pure a : parser α) buffer.nil 0 = done 0 a := by simp [pure_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

instance bind {f : α → parser β} [p.bounded] :
  (p >>= f).bounded :=
begin
  constructor,
  intros cb n hn,
  obtain ⟨_, _, hp⟩ := bounded.exists p hn,
  simp [hp]
end

instance and_then {q : parser β} [p.bounded] : (p >> q).bounded :=
bounded.bind

instance map [p.bounded] {f : α → β} : (f <$> p).bounded :=
bounded.bind

instance seq {f : parser (α → β)} [f.bounded] : (f <*> p).bounded :=
bounded.bind

instance mmap {a : α} {l : list α} {f : α → parser β} [∀ a, (f a).bounded] :
  ((a :: l).mmap f).bounded :=
bounded.bind

instance mmap' {a : α} {l : list α} {f : α → parser β} [∀ a, (f a).bounded] :
  ((a :: l).mmap' f).bounded :=
bounded.and_then

instance failure : @parser.bounded α failure :=
⟨by simp⟩

lemma guard_iff {p : Prop} [decidable p] : bounded (guard p) ↔ ¬ p :=
by simpa [guard, apply_ite bounded, pure, failure] using λ _, bounded.failure

instance orelse [p.bounded] [q.bounded] : (p <|> q).bounded :=
begin
  constructor,
  intros cb n hn,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx;
    exact absurd hn (of_done h).not_le },
  { simp }
end

instance decorate_errors [p.bounded] :
  (@decorate_errors α msgs p).bounded :=
begin
  constructor,
  intros _ _,
  simpa using bounded.exists p
end

lemma decorate_errors_iff : (@parser.decorate_errors α msgs p).bounded ↔ p.bounded :=
begin
  split,
  { introI,
    constructor,
    intros _ _ hn,
    obtain ⟨_, _, h⟩ := bounded.exists (@parser.decorate_errors α msgs p) hn,
    simp [decorate_errors_eq_fail] at h,
    exact h.right.right },
  { introI,
    constructor,
    intros _ _ hn,
    obtain ⟨_, _, h⟩ := bounded.exists p hn,
    simp [h] }
end

instance decorate_error [p.bounded] : (@decorate_error α msg p).bounded :=
bounded.decorate_errors

lemma decorate_error_iff : (@parser.decorate_error α msg p).bounded ↔ p.bounded :=
decorate_errors_iff

instance any_char : bounded any_char :=
⟨λ cb n hn, by simp [any_char, hn]⟩

instance sat {p : char → Prop} [decidable_pred p] : bounded (sat p) :=
⟨λ cb n hn, by simp [sat, hn]⟩

lemma eps : ¬ bounded eps := pure

instance ch {c : char} : bounded (ch c) :=
bounded.decorate_error

lemma char_buf_iff {cb' : char_buffer} : bounded (char_buf cb') ↔ cb' ≠ buffer.nil :=
begin
  have : cb' ≠ buffer.nil ↔ cb'.to_list ≠ [] :=
      not_iff_not_of_iff ⟨λ h, by simp [h], λ h, by simpa using congr_arg list.to_buffer h⟩,
  rw [char_buf, decorate_error_iff, this],
  cases cb'.to_list,
  { simp [pure, ch] },
  { simp only [iff_true, ne.def, not_false_iff],
    apply_instance }
end

instance one_of {cs : list char} : (one_of cs).bounded :=
bounded.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).bounded :=
bounded.and_then

lemma str_iff {s : string} : (str s).bounded ↔ s ≠ "" :=
begin
  rw [str, decorate_error_iff],
  cases hs : s.to_list,
  { have : s = "",
      { cases s, rw [string.to_list] at hs, simpa [hs] },
    simp [pure, this] },
  { have : s ≠ "",
      { intro H, simpa [H] using hs },
    simp only [this, iff_true, ne.def, not_false_iff],
    apply_instance }
end

lemma remaining : ¬ remaining.bounded :=
begin
  introI,
  have : remaining buffer.nil 0 = done 0 0 := by simp [remaining_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

lemma eof : ¬ eof.bounded :=
begin
  introI,
  have : eof buffer.nil 0 = done 0 () := by simp [eof_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

section fold

instance foldr_core_zero {f : α → β → β} : (foldr_core f p b 0).bounded :=
bounded.failure

instance foldl_core_zero {f : β → α → β} {b : β} : (foldl_core f b p 0).bounded :=
bounded.failure

variables {reps : ℕ} [hpb : p.bounded] (he : ∀ cb n n' err, p cb n = fail n' err → n ≠ n')
include hpb he

lemma foldr_core {f : α → β → β} : (foldr_core f p b reps).bounded :=
begin
  cases reps,
  { exact bounded.foldr_core_zero },
  constructor,
  intros cb n hn,
  obtain ⟨np, errp, hp⟩ := bounded.exists p hn,
  simpa [foldr_core_succ_eq_fail, hp] using he cb n np errp,
end

lemma foldr {f : α → β → β} : bounded (foldr f p b) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.foldr_core f p b (cb.size - n + 1)).bounded := foldr_core he,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.foldr_core f p b (cb.size - n + 1)) hn,
  simp [foldr, hp]
end

lemma foldl_core {f : β → α → β} :
  (foldl_core f b p reps).bounded :=
begin
  cases reps,
  { exact bounded.foldl_core_zero },
  constructor,
  intros cb n hn,
  obtain ⟨np, errp, hp⟩ := bounded.exists p hn,
  simpa [foldl_core_succ_eq_fail, hp] using he cb n np errp,
end

lemma foldl {f : β → α → β} : bounded (foldl f b p) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.foldl_core f b p (cb.size - n + 1)).bounded := foldl_core he,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.foldl_core f b p (cb.size - n + 1)) hn,
  simp [foldl, hp]
end

lemma many : p.many.bounded :=
foldr he

omit hpb
lemma many_char {pc : parser char} [pc.bounded]
  (he : ∀ cb n n' err, pc cb n = fail n' err → n ≠ n'): pc.many_char.bounded :=
by { convert bounded.map, exact many he }
include hpb

lemma many' : p.many'.bounded :=
by { convert bounded.and_then, exact many he }

end fold

instance many1 [p.bounded] : p.many1.bounded :=
bounded.seq

instance many_char1 {p : parser char} [p.bounded] : p.many_char1.bounded :=
bounded.map

instance sep_by1 {sep : parser unit} [p.bounded] : bounded (sep_by1 sep p) :=
bounded.seq

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.bounded → (F p).bounded) :
  ∀ (max_depth : ℕ), bounded (fix_core F max_depth)
| 0               := bounded.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.bounded :=
bounded.decorate_error

instance nat : nat.bounded :=
bounded.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.bounded → (F p).bounded) :
  bounded (fix F) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.fix_core F (cb.size - n + 1)).bounded := fix_core hF _,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.fix_core F (cb.size - n + 1)) hn,
  simp [fix, hp]
end

end bounded

namespace unfailing

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma of_bounded [p.bounded] : ¬ unfailing p :=
begin
  introI,
  cases h : p buffer.nil 0,
  { simpa [lt_irrefl] using bounded.of_done h },
  { exact of_fail h }
end

instance pure : unfailing (pure a) :=
⟨λ _ _, by simp [pure_eq_done]⟩

instance bind {f : α → parser β} [p.unfailing] [∀ a, (f a).unfailing] :
  (p >>= f).unfailing :=
⟨λ cb n, begin
  obtain ⟨np, a, hp⟩ := exists_done p cb n,
  simpa [hp, and.comm, and.left_comm, and.assoc] using exists_done (f a) cb np
end⟩

instance and_then {q : parser β} [p.unfailing] [q.unfailing] : (p >> q).unfailing := unfailing.bind

instance map [p.unfailing] {f : α → β} : (f <$> p).unfailing := unfailing.bind

instance seq {f : parser (α → β)} [f.unfailing] [p.unfailing] : (f <*> p).unfailing :=
unfailing.bind

instance mmap {l : list α} {f : α → parser β} [∀ a, (f a).unfailing] : (l.mmap f).unfailing :=
begin
  constructor,
  induction l with hd tl hl,
  { intros,
    simp [pure_eq_done] },
  { intros,
    obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n,
    obtain ⟨n', b, hf⟩ := hl cb np,
    simp [hp, hf, and.comm, and.left_comm, and.assoc, pure_eq_done] }
end

instance mmap' {l : list α} {f : α → parser β} [∀ a, (f a).unfailing] : (l.mmap' f).unfailing :=
begin
  constructor,
  induction l with hd tl hl,
  { intros,
    simp [pure_eq_done] },
  { intros,
    obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n,
    obtain ⟨n', b, hf⟩ := hl cb np,
    simp [hp, hf, and.comm, and.left_comm, and.assoc, pure_eq_done] }
end

lemma failure : ¬ @parser.unfailing α failure :=
begin
  introI h,
  have : (failure : parser α) buffer.nil 0 = fail 0 dlist.empty := by simp,
  exact of_fail this
end

instance guard_true : unfailing (guard true) := unfailing.pure

lemma guard : ¬ unfailing (guard false) :=
unfailing.failure

instance orelse [p.unfailing] : (p <|> q).unfailing :=
⟨λ cb n, by { obtain ⟨_, _, h⟩ := p.exists_done cb n, simp [success_iff, h] }⟩

instance decorate_errors [p.unfailing] :
  (@decorate_errors α msgs p).unfailing :=
⟨λ cb n, by { obtain ⟨_, _, h⟩ := p.exists_done cb n, simp [success_iff, h] }⟩

instance decorate_error [p.unfailing] : (@decorate_error α msg p).unfailing :=
unfailing.decorate_errors

instance any_char : conditionally_unfailing any_char :=
⟨λ _ _ hn, by simp [success_iff, any_char_eq_done, hn]⟩

lemma sat : conditionally_unfailing (sat (λ _, true)) :=
⟨λ _ _ hn, by simp [success_iff, sat_eq_done, hn]⟩

instance eps : unfailing eps := unfailing.pure

instance remaining : remaining.unfailing :=
⟨λ _ _, by simp [success_iff, remaining_eq_done]⟩

lemma foldr_core_zero {f : α → β → β} {b : β} : ¬ (foldr_core f p b 0).unfailing :=
unfailing.failure

instance foldr_core_of_static {f : α → β → β} {b : β} {reps : ℕ} [p.static] [p.unfailing] :
  (foldr_core f p b (reps + 1)).unfailing :=
begin
  induction reps with reps hr,
  { constructor,
    intros cb n,
    obtain ⟨np, a, h⟩ := p.exists_done cb n,
    simpa [foldr_core_eq_done, h] using (static.of_done h).symm },
  { constructor,
    haveI := hr,
    intros cb n,
    obtain ⟨np, a, h⟩ := p.exists_done cb n,
    have : n = np := static.of_done h,
    subst this,
    obtain ⟨np, b', hf⟩ := exists_done (foldr_core f p b (reps + 1)) cb n,
    have : n = np := static.of_done hf,
    subst this,
    refine ⟨n, f a b', _⟩,
    rw foldr_core_eq_done,
    simp [h, hf, and.comm, and.left_comm, and.assoc] }
end

instance foldr_core_one_of_err_static {f : α → β → β} {b : β} [p.static] [p.err_static] :
  (foldr_core f p b 1).unfailing :=
begin
  constructor,
  intros cb n,
  cases h : p cb n,
  { simpa [foldr_core_eq_done, h] using (static.of_done h).symm },
  { simpa [foldr_core_eq_done, h] using (err_static.of_fail h).symm }
end

-- TODO: add foldr and foldl, many, etc, fix_core

lemma digit : ¬ digit.unfailing :=
of_bounded

lemma nat : ¬ nat.unfailing :=
of_bounded

end unfailing

namespace err_static

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma not_of_ne (h : p cb n = fail n' err) (hne : n ≠ n') : ¬ err_static p :=
by { introI, exact hne (of_fail h) }

instance pure : err_static (pure a) :=
⟨λ _ _ _ _, by { simp [pure_eq_done] }⟩

instance bind {f : α → parser β} [p.static] [p.err_static] [∀ a, (f a).err_static] :
  (p >>= f).err_static :=
⟨λ cb n n' err, begin
  rw bind_eq_fail,
  rintro (hp | ⟨_, _, hp, hf⟩),
  { exact of_fail hp },
  { exact trans (static.of_done hp) (of_fail hf) }
end⟩

instance bind_of_unfailing {f : α → parser β} [p.err_static] [∀ a, (f a).unfailing] :
  (p >>= f).err_static :=
⟨λ cb n n' err, begin
  rw bind_eq_fail,
  rintro (hp | ⟨_, _, hp, hf⟩),
  { exact of_fail hp },
  { exact false.elim (unfailing.of_fail hf) }
end⟩

instance and_then {q : parser β} [p.static] [p.err_static] [q.err_static] : (p >> q).err_static :=
err_static.bind

instance and_then_of_unfailing {q : parser β} [p.err_static] [q.unfailing] : (p >> q).err_static :=
err_static.bind_of_unfailing

instance map [p.err_static] {f : α → β} : (f <$> p).err_static :=
⟨λ _ _ _ _, by { rw map_eq_fail, exact of_fail }⟩

instance seq {f : parser (α → β)} [f.static] [f.err_static] [p.err_static] : (f <*> p).err_static :=
err_static.bind

instance seq_of_unfailing {f : parser (α → β)} [f.err_static] [p.unfailing] :
  (f <*> p).err_static :=
err_static.bind_of_unfailing

instance mmap : Π {l : list α} {f : α → parser β}
  [∀ a, (f a).static] [∀ a, (f a).err_static], (l.mmap f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.bind,
  { exact h _ },
  { exact h' _ },
  { intro,
    convert err_static.bind,
    { convert static.mmap,
      exact h },
    { apply mmap,
      { exact h },
      { exact h' } },
    { exact λ _, err_static.pure } }
end

instance mmap_of_unfailing : Π {l : list α} {f : α → parser β}
  [∀ a, (f a).unfailing] [∀ a, (f a).err_static], (l.mmap f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.bind_of_unfailing,
  { exact h' _ },
  { intro,
    convert unfailing.bind,
    { convert unfailing.mmap,
      exact h },
    { exact λ _, unfailing.pure } }
end

instance mmap' : Π {l : list α} {f : α → parser β}
  [∀ a, (f a).static] [∀ a, (f a).err_static], (l.mmap' f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.and_then,
  { exact h _ },
  { exact h' _ },
  { convert mmap',
    { exact h },
    { exact h' } }
end

instance mmap'_of_unfailing : Π {l : list α} {f : α → parser β}
  [∀ a, (f a).unfailing] [∀ a, (f a).err_static], (l.mmap' f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.and_then_of_unfailing,
  { exact h' _ },
  { convert unfailing.mmap',
    exact h }
end

instance failure : @parser.err_static α failure :=
⟨λ _ _ _ _ h, (failure_eq_fail.mp h).left⟩

instance guard {p : Prop} [decidable p] : err_static (guard p) :=
⟨λ _ _ _ _ h, (guard_eq_fail.mp h).right.left⟩

instance orelse [p.err_static] [q.mono] : (p <|> q).err_static :=
⟨λ _ n n' _, begin
  by_cases hn : n = n',
  { exact λ _, hn },
  { rw orelse_eq_fail_of_mono_ne hn,
    { exact of_fail },
    { apply_instance } }
end⟩

instance decorate_errors :
  (@decorate_errors α msgs p).err_static :=
⟨λ _ _ _ _ h, (decorate_errors_eq_fail.mp h).left⟩

instance decorate_error : (@decorate_error α msg p).err_static :=
err_static.decorate_errors

instance any_char : err_static any_char :=
⟨λ _ _ _ _, by { rw [any_char_eq_fail, and.comm], simp }⟩

instance sat_iff {p : char → Prop} [decidable_pred p] : err_static (sat p) :=
⟨λ _ _ _ _ h, (sat_eq_fail.mp h).left⟩

instance eps : err_static eps := err_static.pure

instance ch (c : char) : err_static (ch c) :=
err_static.decorate_error

instance char_buf {cb' : char_buffer} : err_static (char_buf cb') :=
err_static.decorate_error

instance one_of {cs : list char} : err_static (one_of cs) :=
err_static.decorate_errors

instance one_of' {cs : list char} : err_static (one_of' cs) :=
err_static.and_then_of_unfailing

instance str {s : string} : err_static (str s) :=
err_static.decorate_error

instance remaining : remaining.err_static :=
⟨λ _ _ _ _, by simp [remaining_ne_fail]⟩

instance eof : eof.err_static :=
err_static.decorate_error

-- TODO: add foldr and foldl, many, etc, fix_core

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.err_static → (F p).err_static) :
  ∀ (max_depth : ℕ), err_static (fix_core F max_depth)
| 0               := err_static.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.err_static :=
err_static.decorate_error

instance nat : nat.err_static :=
err_static.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.err_static → (F p).err_static) :
  err_static (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact err_static.of_fail h }⟩

end err_static

namespace step

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma not_step_of_static_done [static p] (h : ∃ cb n n' a, p cb n = done n' a) : ¬ step p :=
begin
  introI,
  rcases h with ⟨cb, n, n', a, h⟩,
  have hs := static.of_done h,
  simpa [←hs] using of_done h
end

lemma pure (a : α) : ¬ step (pure a) :=
begin
  apply not_step_of_static_done,
  simp [pure_eq_done]
end

instance bind {f : α → parser β} [p.step] [∀ a, (f a).static] :
  (p >>= f).step :=
⟨λ _ _ _ _, by { simp_rw bind_eq_done, rintro ⟨_, _, hp, hf⟩,
  exact (static.of_done hf) ▸ (of_done hp) }⟩

instance bind' {f : α → parser β} [p.static] [∀ a, (f a).step] :
  (p >>= f).step :=
⟨λ _ _ _ _, by { simp_rw bind_eq_done, rintro ⟨_, _, hp, hf⟩,
  rw static.of_done hp, exact of_done hf }⟩

instance and_then {q : parser β} [p.step] [q.static] : (p >> q).step := step.bind

instance and_then' {q : parser β} [p.static] [q.step] : (p >> q).step := step.bind'

instance map [p.step] {f : α → β} : (f <$> p).step :=
⟨λ _ _ _ _, by { simp_rw map_eq_done, rintro ⟨_, hp, _⟩, exact of_done hp }⟩

instance seq {f : parser (α → β)} [f.step] [p.static] : (f <*> p).step := step.bind

instance seq' {f : parser (α → β)} [f.static] [p.step] : (f <*> p).step := step.bind'

instance mmap {f : α → parser β} [(f a).step] :
  ([a].mmap f).step :=
begin
  convert step.bind,
  { apply_instance },
  { intro,
    convert static.bind,
    { exact static.pure },
    { exact λ _, static.pure } }
end

instance mmap' {f : α → parser β} [(f a).step] :
  ([a].mmap' f).step :=
begin
  convert step.and_then,
  { apply_instance },
  { exact static.pure }
end

instance failure : @parser.step α failure :=
⟨λ _ _ _ _, by simp⟩

lemma guard_true : ¬ step (guard true) := pure _

instance guard : step (guard false) :=
step.failure

instance orelse [p.step] [q.step] : (p <|> q).step :=
⟨λ _ _ _ _, by { simp_rw orelse_eq_done, rintro (h | ⟨h, -⟩); exact of_done h }⟩

lemma decorate_errors_iff : (@parser.decorate_errors α msgs p).step ↔ p.step :=
begin
  split,
  { introI,
    constructor,
    intros cb n n' a h,
    have : (@parser.decorate_errors α msgs p) cb n = done n' a := by simpa using h,
    exact of_done this },
  { introI,
    constructor,
    intros _ _ _ _ h,
    rw decorate_errors_eq_done at h,
    exact of_done h }
end

instance decorate_errors [p.step] :
  (@decorate_errors α msgs p).step :=
⟨λ _ _ _ _, by { rw decorate_errors_eq_done, exact of_done }⟩

lemma decorate_error_iff : (@parser.decorate_error α msg p).step ↔ p.step :=
decorate_errors_iff

instance decorate_error [p.step] : (@decorate_error α msg p).step :=
step.decorate_errors

instance any_char : step any_char :=
begin
  constructor,
  intros cb n,
  simp_rw [any_char_eq_done],
  rintro _ _ ⟨_, rfl, -⟩,
  simp
end

instance sat {p : char → Prop} [decidable_pred p] : step (sat p) :=
begin
  constructor,
  intros cb n,
  simp_rw [sat_eq_done],
  rintro _ _ ⟨_, _, rfl, -⟩,
  simp
end

lemma eps : ¬ step eps := step.pure ()

instance ch {c : char} : step (ch c) := step.decorate_error

lemma char_buf_iff {cb' : char_buffer} : (char_buf cb').step ↔ cb'.size = 1 :=
begin
  have : char_buf cb' cb' 0 = done cb'.size () := by simp [char_buf_eq_done],
  split,
  { introI,
    simpa using of_done this },
  { intro h,
    constructor,
    intros cb n n' _,
    rw [char_buf_eq_done, h],
    rintro ⟨rfl, -⟩,
    refl }
end

instance one_of {cs : list char} : (one_of cs).step :=
step.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).step :=
step.and_then

lemma str_iff {s : string} : (str s).step ↔ s.length = 1 :=
by simp [str_eq_char_buf, char_buf_iff, ←string.to_list_inj, buffer.ext_iff]

lemma remaining : ¬ remaining.step :=
begin
  apply not_step_of_static_done,
  simp [remaining_eq_done]
end

lemma eof : ¬ eof.step :=
begin
  apply not_step_of_static_done,
  simp only [eof_eq_done, exists_eq_left', exists_const],
  use [buffer.nil, 0],
  simp
end

-- TODO: add foldr and foldl, many, etc, fix_core

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.step → (F p).step) :
  ∀ (max_depth : ℕ), step (fix_core F max_depth)
| 0               := step.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.step :=
step.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.step → (F p).step) :
  step (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact of_done h }⟩

end step

section step

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma many1_eq_done_iff_many_eq_done [p.step] [p.bounded] {x : α} {xs : list α} :
  many1 p cb n = done n' (x :: xs) ↔ many p cb n = done n' (x :: xs) :=
begin
  induction hx : (x :: xs) with hd tl IH generalizing x xs n n',
  { simpa using hx },
  split,
  { simp only [many1_eq_done, and_imp, exists_imp_distrib],
    intros np hp hm,
    have : np = n + 1 := step.of_done hp,
    have hn : n < cb.size := bounded.of_done hp,
    subst this,
    obtain ⟨k, hk⟩ : ∃ k, cb.size - n = k + 1 :=
      nat.exists_eq_succ_of_ne_zero (ne_of_gt (tsub_pos_of_lt hn)),
    cases k,
    { cases tl;
      simpa [many_eq_done_nil, nat.sub_succ, hk, many_eq_done, hp, foldr_core_eq_done] using hm },
    cases tl with hd' tl',
    { simpa [many_eq_done_nil, nat.sub_succ, hk, many_eq_done, hp, foldr_core_eq_done] using hm },
    { rw ←@IH hd' tl' at hm, swap, refl,
      simp only [many1_eq_done, many, foldr] at hm,
      obtain ⟨np, hp', hf⟩ := hm,
      have : np = n + 1 + 1 := step.of_done hp',
      subst this,
      simpa [nat.sub_succ, many_eq_done, hp, hk, foldr_core_eq_done, hp'] using hf } },
  { simp only [many_eq_done, many1_eq_done, and_imp, exists_imp_distrib],
    intros np hp hm,
    have : np = n + 1 := step.of_done hp,
    have hn : n < cb.size := bounded.of_done hp,
    subst this,
    obtain ⟨k, hk⟩ : ∃ k, cb.size - n = k + 1 :=
      nat.exists_eq_succ_of_ne_zero (ne_of_gt (tsub_pos_of_lt hn)),
    cases k,
    { cases tl;
      simpa [many_eq_done_nil, nat.sub_succ, hk, many_eq_done, hp, foldr_core_eq_done] using hm },
    cases tl with hd' tl',
    { simpa [many_eq_done_nil, nat.sub_succ, hk, many_eq_done, hp, foldr_core_eq_done] using hm },
    { simp [hp],
      rw ←@IH hd' tl' (n + 1) n', swap, refl,
      rw [hk, foldr_core_eq_done, or.comm] at hm,
      obtain (hm | ⟨np, hd', tl', hp', hf, hm⟩) := hm,
      { simpa using hm },
      simp only at hm,
      obtain ⟨rfl, rfl⟩ := hm,
      have : np = n + 1 + 1 := step.of_done hp',
      subst this,
      simp [nat.sub_succ, many, many1_eq_done, hp, hk, foldr_core_eq_done, hp', ←hf, foldr] } }
end

end step

namespace prog

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

@[priority 100] -- see Note [lower instance priority]
instance of_step [step p] : prog p :=
⟨λ _ _ _ _ h, by { rw step.of_done h, exact nat.lt_succ_self _ }⟩

lemma pure (a : α) : ¬ prog (pure a) :=
begin
  introI h,
  have : (pure a : parser α) buffer.nil 0 = done 0 a := by simp [pure_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

instance bind {f : α → parser β} [p.prog] [∀ a, (f a).mono] :
  (p >>= f).prog :=
⟨λ _ _ _ _, by { simp_rw bind_eq_done, rintro ⟨_, _, hp, hf⟩,
  exact lt_of_lt_of_le (of_done hp) (mono.of_done hf) }⟩

instance and_then {q : parser β} [p.prog] [q.mono] : (p >> q).prog := prog.bind

instance map [p.prog] {f : α → β} : (f <$> p).prog :=
⟨λ _ _ _ _, by { simp_rw map_eq_done, rintro ⟨_, hp, _⟩, exact of_done hp }⟩

instance seq {f : parser (α → β)} [f.prog] [p.mono] : (f <*> p).prog := prog.bind

instance mmap {l : list α} {f : α → parser β} [(f a).prog] [∀ a, (f a).mono] :
  ((a :: l).mmap f).prog :=
begin
  constructor,
  simp only [and_imp, bind_eq_done, return_eq_pure, mmap, exists_imp_distrib, pure_eq_done],
  rintro _ _ _ _ _ _ h _ _ hp rfl rfl,
  exact lt_of_lt_of_le (of_done h) (mono.of_done hp)
end

instance mmap' {l : list α} {f : α → parser β} [(f a).prog] [∀ a, (f a).mono] :
  ((a :: l).mmap' f).prog :=
begin
  constructor,
  simp only [and_imp, bind_eq_done, mmap', exists_imp_distrib, and_then_eq_bind],
  intros _ _ _ _ _ _ h hm,
  exact lt_of_lt_of_le (of_done h) (mono.of_done hm)
end

instance failure : @parser.prog α failure :=
prog.of_step

lemma guard_true : ¬ prog (guard true) := pure _

instance guard : prog (guard false) :=
prog.failure

instance orelse [p.prog] [q.prog] : (p <|> q).prog :=
⟨λ _ _ _ _, by { simp_rw orelse_eq_done, rintro (h | ⟨h, -⟩); exact of_done h }⟩

lemma decorate_errors_iff : (@parser.decorate_errors α msgs p).prog ↔ p.prog :=
begin
  split,
  { introI,
    constructor,
    intros cb n n' a h,
    have : (@parser.decorate_errors α msgs p) cb n = done n' a := by simpa using h,
    exact of_done this },
  { introI,
    constructor,
    intros _ _ _ _ h,
    rw decorate_errors_eq_done at h,
    exact of_done h }
end

instance decorate_errors [p.prog] :
  (@decorate_errors α msgs p).prog :=
⟨λ _ _ _ _, by { rw decorate_errors_eq_done, exact of_done }⟩

lemma decorate_error_iff : (@parser.decorate_error α msg p).prog ↔ p.prog :=
decorate_errors_iff

instance decorate_error [p.prog] : (@decorate_error α msg p).prog :=
prog.decorate_errors

instance any_char : prog any_char :=
prog.of_step

instance sat {p : char → Prop} [decidable_pred p] : prog (sat p) :=
prog.of_step

lemma eps : ¬ prog eps := prog.pure ()

instance ch {c : char} : prog (ch c) :=
prog.of_step

lemma char_buf_iff {cb' : char_buffer} : (char_buf cb').prog ↔ cb' ≠ buffer.nil :=
begin
  have : cb' ≠ buffer.nil ↔ cb'.to_list ≠ [] :=
      not_iff_not_of_iff ⟨λ h, by simp [h], λ h, by simpa using congr_arg list.to_buffer h⟩,
  rw [char_buf, this, decorate_error_iff],
  cases cb'.to_list,
  { simp [pure] },
  { simp only [iff_true, ne.def, not_false_iff],
    apply_instance }
end

instance one_of {cs : list char} : (one_of cs).prog :=
prog.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).prog :=
prog.and_then

lemma str_iff {s : string} : (str s).prog ↔ s ≠ "" :=
by simp [str_eq_char_buf, char_buf_iff, ←string.to_list_inj, buffer.ext_iff]

lemma remaining : ¬ remaining.prog :=
begin
  introI h,
  have : remaining buffer.nil 0 = done 0 0 := by simp [remaining_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

lemma eof : ¬ eof.prog :=
begin
  introI h,
  have : eof buffer.nil 0 = done 0 () := by simpa [remaining_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

-- TODO: add foldr and foldl, many, etc, fix_core

instance many1 [p.mono] [p.prog] : p.many1.prog :=
begin
  constructor,
  rintro cb n n' (_ | ⟨hd, tl⟩),
  { simp },
  { rw many1_eq_done,
    rintro ⟨np, hp, h⟩,
    exact (of_done hp).trans_le (mono.of_done h) }
end

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.prog → (F p).prog) :
  ∀ (max_depth : ℕ), prog (fix_core F max_depth)
| 0               := prog.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.prog :=
prog.of_step

instance nat : nat.prog :=
prog.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.prog → (F p).prog) :
  prog (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact of_done h }⟩

end prog

variables {α β : Type} {msgs : thunk (list string)} {msg : thunk string}
variables {p q : parser α} {cb : char_buffer} {n n' : ℕ} {err : dlist string}
variables {a : α} {b : β}

section many

-- TODO: generalize to p.prog instead of p.step
lemma many_sublist_of_done [p.step] [p.bounded] {l : list α}
  (h : p.many cb n = done n' l) :
  ∀ k < n' - n, p.many cb (n + k) = done n' (l.drop k) :=
begin
  induction l with hd tl hl generalizing n,
  { rw many_eq_done_nil at h,
    simp [h.left] },
  intros m hm,
  cases m,
  { exact h },
  rw [list.drop, nat.add_succ, ←nat.succ_add],
  apply hl,
  { rw [←many1_eq_done_iff_many_eq_done, many1_eq_done] at h,
    obtain ⟨_, hp, h⟩ := h,
    convert h,
    exact (step.of_done hp).symm },
  { exact nat.lt_pred_iff.mpr hm },
end

lemma many_eq_nil_of_done [p.step] [p.bounded] {l : list α}
  (h : p.many cb n = done n' l) :
  p.many cb n' = done n' [] :=
begin
  induction l with hd tl hl generalizing n,
  { convert h,
    rw many_eq_done_nil at h,
    exact h.left.symm },
  { rw [←many1_eq_done_iff_many_eq_done, many1_eq_done] at h,
    obtain ⟨_, -, h⟩ := h,
    exact hl h }
end

lemma many_eq_nil_of_out_of_bound [p.bounded] {l : list α}
  (h : p.many cb n = done n' l) (hn : cb.size < n) :
  n' = n ∧ l = [] :=
begin
  cases l,
  { rw many_eq_done_nil at h,
    exact ⟨h.left.symm, rfl⟩ },
  { rw many_eq_done at h,
    obtain ⟨np, hp, -⟩ := h,
    exact absurd (bounded.of_done hp) hn.not_lt }
end

lemma many1_length_of_done [p.mono] [p.step] [p.bounded] {l : list α}
  (h : many1 p cb n = done n' l) :
  l.length = n' - n :=
begin
  induction l with hd tl hl generalizing n n',
  { simpa using h },
  { obtain ⟨k, hk⟩ : ∃ k, n' = n + k + 1 := nat.exists_eq_add_of_lt (prog.of_done h),
    subst hk,
    simp only [many1_eq_done] at h,
    obtain ⟨_, hp, h⟩ := h,
    have := step.of_done hp,
    subst this,
    cases tl,
    { simp only [many_eq_done_nil, add_left_inj, exists_and_distrib_right, self_eq_add_right] at h,
      rcases h with ⟨rfl, -⟩,
      simp },
    rw ←many1_eq_done_iff_many_eq_done at h,
    specialize hl h,
    simp [hl, add_comm, add_assoc, nat.sub_succ] }
end

lemma many1_bounded_of_done [p.step] [p.bounded] {l : list α}
  (h : many1 p cb n = done n' l) :
  n' ≤ cb.size :=
begin
  induction l with hd tl hl generalizing n n',
  { simpa using h },
  { simp only [many1_eq_done] at h,
    obtain ⟨np, hp, h⟩ := h,
    have := step.of_done hp,
    subst this,
    cases tl,
    { simp only [many_eq_done_nil, exists_and_distrib_right] at h,
      simpa [←h.left] using bounded.of_done hp },
    { rw ←many1_eq_done_iff_many_eq_done at h,
      exact hl h } }
end

end many

section nat
/--
The `val : ℕ` produced by a successful parse of a `cb : char_buffer` is the numerical value
represented by the string of decimal digits (possibly padded with 0s on the left)
starting from the parsing position `n` and ending at position `n'`. The number
of characters parsed in is necessarily `n' - n`.

This is one of the directions of `nat_eq_done`.
-/
lemma nat_of_done {val : ℕ} (h : nat cb n = done n' val) :
  val = (nat.of_digits 10 ((((cb.to_list.drop n).take (n' - n)).reverse.map
          (λ c, c.to_nat - '0'.to_nat)))) :=
begin
  /- The parser `parser.nat` that generates a decimal number from a string of digit characters does
  several things. First it ingests in as many digits as it can with `many1 digit`. Then, it folds
  over the resulting `list ℕ` using a helper function that keeps track of both the running sum an
  and the magnitude so far, using a `(sum, magnitude) : (ℕ × ℕ)` pair. The final sum is extracted
  using a `prod.fst`.

  To prove that the value that `parser.nat` produces, after moving precisely `n' - n` steps, is
  precisely what `nat.of_digits` would give, if supplied the string that is in the ingested
  `char_buffer` (modulo conversion from `char` to `ℕ ), we need to induct over the length `n' - n`
  of `cb : char_buffer` ingested, and prove that the parser must have terminated due to hitting
  either the end of the `char_buffer` or a non-digit character.

  The statement of the lemma is phrased using a combination of `list.drop` and `list.map` because
  there is no currently better way to extract an "interval" from a `char_buffer`. Additionally, the
  statement uses a `list.reverse` because `nat.of_digits` is little-endian.

  We try to stop referring to the `cb : char_buffer` as soon as possible, so that we can instead
  regard a `list char` instead, which lends itself better to proofs via induction.
  -/
  /- We first prove some helper lemmas about the definition of `parser.nat`. Since it is defined
  in core, we have to work with how it is defined instead of changing its definition.
  In its definition, the function that folds over the parsed in digits is defined internally,
  as a lambda with anonymous destructor syntax, which leads to an unpleasant `nat._match_1` term
  when rewriting the definition of `parser.nat` away. Since we know exactly what the function is,
  we have a `rfl`-like lemma here to rewrite it back into a readable form.
  -/
  have natm : nat._match_1 = (λ (d : ℕ) p, ⟨p.1 + d * p.2, p.2 * 10⟩),
  { ext1, ext1 ⟨⟩, refl },
  -- We also have to prove what is the `prod.snd` of the result of the fold of a `list (ℕ × ℕ)` with
  -- the function above. We use this lemma later when we finish our inductive case.
  have hpow : ∀ l, (list.foldr (λ (digit : ℕ) (x : ℕ × ℕ), (x.fst + digit * x.snd, x.snd * 10))
    (0, 1) l).snd = 10 ^ l.length,
  { intro l,
    induction l with hd tl hl,
    { simp },
    { simp [hl, pow_succ, mul_comm] } },
  -- We convert the hypothesis that `parser.nat` has succeeded into an existential that there is
  -- some list of digits that it has parsed in, and that those digits, when folded over by the
  -- function above, give the value at hand.
  simp only [nat, pure_eq_done, natm, decorate_error_eq_done, bind_eq_done] at h,
  obtain ⟨n', l, hp, rfl, rfl⟩ := h,
  -- We now want to stop working with the `cb : char_buffer` and parse positions `n` and `n'`,
  -- and just deal with the parsed digit list `l : list ℕ`. To do so, we have to show that
  -- this is precisely the list that could have been parsed in, no smaller and no greater.
  induction l with lhd ltl IH generalizing n n' cb,
  { -- Base case: we parsed in no digits whatsoever. But this is impossible because `parser.many1`
    -- must produce a list that is not `list.nil`, by `many1_ne_done_nil`.
    simpa using hp },
  -- Inductive case:
  -- We must prove that the first digit parsed in `lhd : ℕ` is precisely the digit that is
  -- represented by the character at position `n` in `cb : char_buffer`.
  -- We will also prove the correspondence between the subsequent digits `ltl : list ℕ` and the
  -- remaining characters past position `n` up to position `n'`.
  cases hx : (list.drop n (buffer.to_list cb)) with chd ctl,
  { -- Are there even characters left to parse, at position `n` in the `cb : char_buffer`? In other
    -- words, are we already out of bounds, and thus could not have parsed in any value
    -- successfully. But this must be a contradiction because `parser.digit` is a `bounded` parser,
    -- (due to its being defined via `parser.decorate_error`), which means it only succeeds
    -- in-bounds, and the `many1` parser combinator retains that property.
    have : cb.size ≤ n := by simpa using list.drop_eq_nil_iff_le.mp hx,
    exact absurd (bounded.of_done hp) this.not_lt },
  -- We prove that the first digit parsed in is precisely the digit that is represented by the
  -- character at position `n`, which we now call `chd : char`.
  have chdh : chd.to_nat - '0'.to_nat = lhd,
    { simp only [many1_eq_done] at hp,
      -- We know that `parser.digit` succeeded, so it has moved to a possibly different position.
      -- In fact, we know that this new position is `n + 1`, by the `step` property of
      -- `parser.digit`.
      obtain ⟨_, hp, -⟩ := hp,
      have := step.of_done hp,
      subst this,
      -- We now unfold what it means for `parser.digit` to succeed, which means that the character
      -- parsed in was "numeric" (for some definition of that property), and, more importantly,
      -- that the `n`th character of `cb`, let's say `c`, when converted to a `ℕ` via
      -- `char.to_nat c - '0'.to_nat`, must be equal to the resulting value, `lhd` in our case.
      simp only [digit_eq_done, buffer.read_eq_nth_le_to_list, hx, buffer.length_to_list, true_and,
                 add_left_inj, list.length, list.nth_le, eq_self_iff_true, exists_and_distrib_left,
                 fin.coe_mk] at hp,
      rcases hp with ⟨_, hn, rfl, _, _⟩,
      -- But we already know the list corresponding to `cb : char_buffer` from position `n` and on
      -- is equal to `(chd :: ctl) : list char`, so our `c` above must satisfy `c = chd`.
      have hn' : n < cb.to_list.length := by simpa using hn,
      rw ←list.cons_nth_le_drop_succ hn' at hx,
      -- We can ignore proving any correspondence of `ctl : list char` to the other portions of the
      -- `cb : char_buffer`.
      simp only at hx,
      simp [hx] },
  -- We know that we parsed in more than one character because of the `prog` property of
  -- `parser.digit`, which the `many1` parser combinator retains. In other words, we know that
  -- `n < n'`, and so, the list of digits `ltl` must correspond to the list of digits that
  -- `digit.many1 cb (n + 1)` would produce. We know that the shift of `1` in `n ↦ n + 1` holds
  -- due to the `step` property of `parser.digit`.
  -- We also get here `k : ℕ` which will indicate how many characters we parsed in past position
  -- `n`. We will prove later that this must be the number of digits we produced as well in `ltl`.
  obtain ⟨k, hk⟩ : ∃ k, n' = n + k + 1 := nat.exists_eq_add_of_lt (prog.of_done hp),
  have hdm : ltl = [] ∨ digit.many1 cb (n + 1) = done n' ltl,
  { cases ltl,
    { simp },
    { rw many1_eq_done at hp,
      obtain ⟨_, hp, hp'⟩ := hp,
      simpa [step.of_done hp, many1_eq_done_iff_many_eq_done] using hp' } },
  -- Now we case on the two possibilities, that there was only a single digit parsed in, and
  -- `ltl = []`, or, had we started parsing at `n + 1` instead, we'd parse in the value associated
  -- with `ltl`.
  -- We prove that the LHS, which is a fold over a `list ℕ` is equal to the RHS, which is that
  -- the `val : ℕ` that `nat.of_digits` produces when supplied a `list ℕ that has been produced
  -- via mapping a `list char` using `char.to_nat`. Specifically, that `list char` are the
  -- characters in the `cb : char_buffer`, from position `n` to position `n'` (excluding `n'`),
  -- in reverse.
  rcases hdm with rfl|hdm,
  { -- Case that `ltl = []`.
    simp only [many1_eq_done, many_eq_done_nil, exists_and_distrib_right] at hp,
    -- This means we must have failed parsing with `parser.digit` at some other position,
    -- which we prove must be `n + 1` via the `step` property.
    obtain ⟨_, hp, rfl, hp'⟩ := hp,
    have := step.of_done hp,
    subst this,
    -- Now we rely on the simplifier, which simplfies the LHS, which is a fold over a singleton
    -- list. On the RHS, `list.take (n + 1 - n)` also produces a singleton list, which, when
    -- reversed, is the same list. `nat.of_digits` of a singleton list is precisely the value in
    -- the list. And we already have that `chd.to_nat - '0'.to_nat = lhd`.
    simp [chdh] },
  -- We now have to deal with the case where we parsed in more than one digit, and thus
  -- `n + 1 < n'`, which means `ctl` has one or more elements. Similarly, `ltl` has one or more
  -- elements.
  -- We finish ridding ourselves of references to `cb : char_buffer`, by relying on the fact that
  -- our `ctl : list char` must be the appropriate portion of `cb` once enough elements have been
  -- dropped and taken.
  have rearr :
    list.take (n + (k + 1) - (n + 1)) (list.drop (n + 1) (buffer.to_list cb)) = ctl.take k,
  { simp [←list.tail_drop, hx, nat.sub_succ, hk] },
  -- We have to prove that the number of digits produced (given by `ltl`) is equal to the number
  -- of characters parsed in, as given by `ctl.take k`, and that this is precisely `k`. We phrase it
  -- in the statement using `min`, because lemmas about `list.length (list.take ...)` simplify to
  -- a statement that uses `min`. The `list.length` term appears from the reduction of the folding
  -- function, as proven above.
  have ltll : min k ctl.length = ltl.length,
  { -- Here is an example of how statements about the `list.length` of `list.take` simplify.
    have : (ctl.take k).length = min k ctl.length := by simp,
    -- We bring back the underlying definition of `ctl` as the result of a sequence of `list.take`
    -- and `list.drop`, so that lemmas about `list.length` of those can fire.
    rw [←this, ←rearr, many1_length_of_done hdm],
    -- Likewise, we rid ourselves of the `k` we generated earlier.
    have : k = n' - n - 1,
      { simp [hk, add_assoc] },
    subst this,
    simp only [nat.sub_succ, add_comm, ←nat.pred_sub, buffer.length_to_list, nat.pred_one_add,
                min_eq_left_iff, list.length_drop, add_tsub_cancel_left, list.length_take,
                tsub_zero],
    -- We now have a goal of proving an inequality dealing with `nat` subtraction and `nat.pred`,
    -- both of which require special care to provide positivity hypotheses.
    rw [tsub_le_tsub_iff_right, nat.pred_le_iff],
    { -- We know that `n' ≤ cb.size` because of the `bounded` property, that a parser will not
      -- produce a `done` result at a position farther than the size of the underlying
      -- `char_buffer`.
      convert many1_bounded_of_done hp,
      -- What is now left to prove is that `0 < cb.size`, which can be rephrased
      -- as proving that it is nonempty.
      cases hc : cb.size,
      { -- Proof by contradiction. Let's say that `cb.size = 0`. But we know that we succeeded
        -- parsing in at position `n` using a `bounded` parser, so we must have that
        -- `n < cb.size`.
        have := bounded.of_done hp,
        rw hc at this,
        -- But then `n < 0`, a contradiction.
        exact absurd n.zero_le this.not_le },
      { simp } },
    { -- Here, we use the same result as above, that `n < cb.size`, and relate it to
      -- `n ≤ cb.size.pred`.
      exact nat.le_pred_of_lt (bounded.of_done hp) } },
  -- Finally, we simplify. On the LHS, we have a fold over `lhd :: ltl`, which simplifies to
  -- the operation of the summing folding function on `lhd` and the fold over `ltl`. To that we can
  -- apply the induction hypothesis, because we know that our parser would have succeeded had we
  -- started at position `n + 1`. We replace mentions of `cb : char_buffer` with the appropriate
  -- `chd :: ctl`, replace `lhd` with the appropriate statement of how it is calculated from `chd`,
  -- and use the lemmas describing the length of `ltl` and how it is associated with `k`. We also
  -- remove mentions of `n'` and replace with an expression using solely `n + k + 1`.
  -- We use the lemma we proved above about how the folding function produces the
  -- `prod.snd` value, which is `10` to the power of the length of the list provided to the fold.
  -- Finally, we rely on `nat.of_digits_append` for the related statement of how digits given
  -- are used in the `nat.of_digits` calculation, which also involves `10 ^ list.length ...`.
  -- The `list.append` operation appears due to the `list.reverse (chd :: ctl)`.
  -- We include some addition and multiplication lemmas to help the simplifier rearrange terms.
  simp [IH _ hdm, hx, hk, rearr, ←chdh, ←ltll, hpow, add_assoc, nat.of_digits_append, mul_comm]
end

/--
If we know that `parser.nat` was successful, starting at position `n` and ending at position `n'`,
then it must be the case that for all `k : ℕ`, `n ≤ k`, `k < n'`, the character at the `k`th
position in `cb : char_buffer` is "numeric", that is, is between `'0'` and `'9'` inclusive.

This is a necessary part of proving one of the directions of `nat_eq_done`.
-/
lemma nat_of_done_as_digit {val : ℕ} (h : nat cb n = done n' val) :
  ∀ (hn : n' ≤ cb.size) k (hk : k < n'), n ≤ k →
    '0' ≤ cb.read ⟨k, hk.trans_le hn⟩ ∧ cb.read ⟨k, hk.trans_le hn⟩ ≤ '9' :=
begin
  -- The properties to be shown for the characters involved rely solely on the success of
  -- `parser.digit` at the relevant positions, and not on the actual value `parser.nat` produced.
  -- We break done the success of `parser.nat` into the `parser.digit` success and throw away
  -- the resulting value given by `parser.nat`, and focus solely on the `list ℕ` generated by
  -- `parser.digit.many1`.
  simp only [nat, pure_eq_done, and.left_comm, decorate_error_eq_done, bind_eq_done,
             exists_eq_left, exists_and_distrib_left] at h,
  obtain ⟨xs, h, -⟩ := h,
  -- We want to avoid having to make statements about the `cb : char_buffer` itself. Instead, we
  -- induct on the `xs : list ℕ` that `parser.digit.many1` produced.
  induction xs with hd tl hl generalizing n n',
  { -- Base case: `xs` is empty. But this is a contradiction because `many1` always produces a
    -- nonempty list, as proven by `many1_ne_done_nil`.
    simpa using h },
  -- Inductive case: we prove that the `parser.digit.many1` produced a valid `(hd :: tl) : list ℕ`,
  -- by showing that is the case for the character at position `n`, which gave `hd`, and use the
  -- induction hypothesis on the remaining `tl`.
  -- We break apart a `many1` success into a success of the underlying `parser.digit` to give `hd`
  -- and a `parser.digit.many` which gives `tl`. We first deal with the `hd`.
  rw many1_eq_done at h,
  -- Right away, we can throw away the information about the "new" position that `parser.digit`
  -- ended on because we will soon prove that it must have been `n + 1`.
  obtain ⟨_, hp, h⟩ := h,
  -- The main lemma here is `digit_eq_done`, which already proves the necessary conditions about
  -- the character at hand. What is left to do is properly unpack the information.
  simp only [digit_eq_done, and.comm, and.left_comm, digit_eq_fail, true_and, exists_eq_left,
             eq_self_iff_true, exists_and_distrib_left, exists_and_distrib_left] at hp,
  obtain ⟨rfl, -, hn, ge0, le9, rfl⟩ := hp,
  -- Let's now consider a position `k` between `n` and `n'`, excluding `n'`.
  intros hn k hk hk',
  -- What if we are at `n`? What if we are past `n`? We case on the `n ≤ k`.
  rcases hk'.eq_or_lt with rfl|hk',
  { -- The `n = k` case. But this is exactly what we know already, so we provide the
    -- relevant hypotheses.
    exact ⟨ge0, le9⟩ },
  -- The `n < k` case. First, we check if there would have even been digits parsed in. So, we
  -- case on `tl : list ℕ`
  cases tl,
  { -- Case where `tl = []`. But that means `many` gave us a `[]` so either the character at
    -- position `k` was not "numeric" or we are out of bounds. More importantly, when `many`
    -- successfully produces a `[]`, it does not progress the parser head, so we have that
    -- `n + 1 = n'`. This will lead to a contradiction because now we have `n < k` and `k < n + 1`.
    simp only [many_eq_done_nil, exists_and_distrib_right] at h,
    -- Extract out just the `n + 1 = n'`.
    obtain ⟨rfl, -⟩ := h,
    -- Form the contradictory hypothesis, and discharge the goal.
    have : k < k := hk.trans_le (nat.succ_le_of_lt hk'),
    exact absurd this (lt_irrefl _) },
  { -- Case where `tl ≠ []`. But that means that `many` produced a nonempty list as a result, so
    -- `many1` would have successfully parsed at this position too. We use this statement to
    -- rewrite our hypothesis into something that works with the induction hypothesis, and apply it.
    rw ←many1_eq_done_iff_many_eq_done at h,
    apply hl h,
    -- All that is left to prove is that our `k` is at least our new "lower bound" `n + 1`, which
    -- we have from our original split of the `n ≤ k`, since we are now on the `n < k` case.
    exact nat.succ_le_of_lt hk' }
end

/--
If we know that `parser.nat` was successful, starting at position `n` and ending at position `n'`,
then it must be the case that for the ending position `n'`, either it is beyond the end of the
`cb : char_buffer`, or the character at that position is not "numeric", that is,  between `'0'` and
`'9'` inclusive.

This is a necessary part of proving one of the directions of `nat_eq_done`.
-/
lemma nat_of_done_bounded {val : ℕ} (h : nat cb n = done n' val) :
  ∀ (hn : n' < cb.size), '0' ≤ cb.read ⟨n', hn⟩ → '9' < cb.read ⟨n', hn⟩ :=
begin
  -- The properties to be shown for the characters involved rely solely on the success of
  -- `parser.digit` at the relevant positions, and not on the actual value `parser.nat` produced.
  -- We break done the success of `parser.nat` into the `parser.digit` success and throw away
  -- the resulting value given by `parser.nat`, and focus solely on the `list ℕ` generated by
  -- `parser.digit.many1`.
  -- We deal with the case of `n'` is "out-of-bounds" right away by requiring that
  -- `∀ (hn : n' < cb.size)`. Thus we only have to prove the lemma for the cases where `n'` is still
  -- "in-bounds".
  simp only [nat, pure_eq_done, and.left_comm, decorate_error_eq_done, bind_eq_done,
             exists_eq_left, exists_and_distrib_left] at h,
  obtain ⟨xs, h, -⟩ := h,
  -- We want to avoid having to make statements about the `cb : char_buffer` itself. Instead, we
  -- induct on the `xs : list ℕ` that `parser.digit.many1` produced.
  induction xs with hd tl hl generalizing n n',
  { -- Base case: `xs` is empty. But this is a contradiction because `many1` always produces a
    -- nonempty list, as proven by `many1_ne_done_nil`.
    simpa using h },
  -- Inductive case: at least one character has been parsed in, starting at position `n`.
  -- We know that the size of `cb : char_buffer` must be at least `n + 1` because
  -- `parser.digit.many1` is `bounded` (`n < cb.size`).
  -- We show that either we parsed in just that one character, or we use the inductive hypothesis.
  obtain ⟨k, hk⟩ : ∃ k, cb.size = n + k + 1 := nat.exists_eq_add_of_lt (bounded.of_done h),
  cases tl,
  { -- Case where `tl = []`, so we parsed in only `hd`. That must mean that `parser.digit` failed
    -- at `n + 1`.
    simp only [many1_eq_done, many_eq_done_nil, and.left_comm, exists_and_distrib_right,
               exists_eq_left] at h,
    -- We throw away the success information of what happened at position `n`, and we do not need
    -- the "error" value that the failure produced.
    obtain ⟨-, _, h⟩ := h,
    -- If `parser.digit` failed at `n + 1`, then either we hit a non-numeric character, or
    -- we are out of bounds. `digit_eq_fail` provides us with those two cases.
    simp only [digit_eq_done, and.comm, and.left_comm, digit_eq_fail, true_and, exists_eq_left,
               eq_self_iff_true, exists_and_distrib_left] at h,
    obtain (⟨rfl, h⟩ | ⟨h, -⟩) := h,
    { -- First case: we are still in bounds, but the character is not numeric. We must prove
      -- that we are still in bounds. But we know that from our initial requirement.
      intro hn,
      simpa using h hn },
    { -- Second case: we are out of bounds, and somehow the fold that `many1` relied on failed.
      -- But we know that `parser.digit` is mono, that is, it never goes backward in position,
      -- in neither success nor in failure. We also have that `foldr_core` respects `mono`.
      -- But in this case, `foldr_core` is starting at position `n' + 1` but failing at
      -- position `n'`, which is a contradiction, because otherwise we would have `n' + 1 ≤ n'`.
      simpa using mono.of_fail h } },
  { -- Case where `tl ≠ []`. But that means that `many` produced a nonempty list as a result, so
    -- `many1` would have successfully parsed at this position too. We use this statement to
    -- rewrite our hypothesis into something that works with the induction hypothesis, and apply it.
    rw many1_eq_done at h,
    obtain ⟨_, -, h⟩ := h,
    rw ←many1_eq_done_iff_many_eq_done at h,
    exact hl h }
end

/--
The `val : ℕ` produced by a successful parse of a `cb : char_buffer` is the numerical value
represented by the string of decimal digits (possibly padded with 0s on the left)
starting from the parsing position `n` and ending at position `n'`, where `n < n'`. The number
of characters parsed in is necessarily `n' - n`. Additionally, all of the characters in the `cb`
starting at position `n` (inclusive) up to position `n'` (exclusive) are "numeric", in that they
are between `'0'` and `'9'` inclusive. Such a `char_buffer` would produce the `ℕ` value encoded
by its decimal characters.
-/
lemma nat_eq_done {val : ℕ} : nat cb n = done n' val ↔ ∃ (hn : n < n'),
  val = (nat.of_digits 10 ((((cb.to_list.drop n).take (n' - n)).reverse.map
          (λ c, c.to_nat - '0'.to_nat)))) ∧ (∀ (hn' : n' < cb.size),
          ('0' ≤ cb.read ⟨n', hn'⟩ → '9' < cb.read ⟨n', hn'⟩)) ∧ ∃ (hn'' : n' ≤ cb.size),
          (∀ k (hk : k < n'), n ≤ k →
          '0' ≤ cb.read ⟨k, hk.trans_le hn''⟩ ∧ cb.read ⟨k, hk.trans_le hn''⟩ ≤ '9') :=
begin
  -- To prove this iff, we have most of the way in the forward direction, using the lemmas proven
  -- above. First, we must use that `parser.nat` is `prog`, which means that on success, it must
  -- move forward. We also have to prove the statement that a success means the parsed in
  -- characters were properly "numeric". It involves first generating ane existential witness
  -- that the parse was completely "in-bounds".
  -- For the reverse direction, we first discharge the goals that deal with proving that our parser
  -- succeeded because it encountered characters with the proper "numeric" properties, was
  -- "in-bounds" and hit a nonnumeric character. The more difficult portion is proving that the
  -- list of characters from positions `n` to `n'`, when folded over by the function defined inside
  -- `parser.nat` gives exactly the same value as `nat.of_digits` when supplied with the same
  -- (modulo rearrangement) list. To reach this goal, we try to remove any reliance on the
  -- underlying `cb : char_buffer` or parsers as soon as possible, via a cased-induction.
  refine ⟨λ h, ⟨prog.of_done h, nat_of_done h, nat_of_done_bounded h, _⟩, _⟩,
  { -- To provide the existential witness that `n'` is within the bounds of the `cb : char_buffer`,
    -- we rely on the fact that `parser.nat` is primarily a `parser.digit.many1`, and that `many1`,
    -- must finish with the bounds of the `cb`, as long as the underlying parser is `step` and
    -- `bounded`, which `digit` is. We do not prove this as a separate lemma about `parser.nat`
    -- because it would almost always be only relevant in this larger theorem.
    -- We clone the success hypothesis `h` so that we can supply it back later.
    have H := h,
    -- We unwrap the `parser.nat` success down to the `many1` success, throwing away other info.
    rw [nat] at h,
    simp only [decorate_error_eq_done, bind_eq_done, pure_eq_done, and.left_comm, exists_eq_left,
               exists_and_distrib_left] at h,
    obtain ⟨_, h, -⟩ := h,
    -- Now we get our existential witness that `n' ≤ cb.size`.
    replace h := many1_bounded_of_done h,
    -- With that, we can use the lemma proved above that our characters are "numeric"
    exact ⟨h, nat_of_done_as_digit H h⟩ },
  -- We now prove that given the `cb : char_buffer` with characters within the `n ≤ k < n'` interval
  -- properly "numeric" and such that their `nat.of_digits` generates the `val : ℕ`, `parser.nat`
  -- of that `cb`, when starting at `n`, will finish at `n'` and produce the same `val`.
  -- We first introduce the relevant hypotheses, including the fact that we have a valid interval
  -- where `n < n'` and that characters at `n'` and beyond are no longer numeric.
  rintro ⟨hn, hv, hb, hn', ho⟩,
  -- We first unwrap the `parser.nat` definition to the underlying `parser.digit.many1` success
  -- and the fold function of the digits.
  rw nat,
  simp only [and.left_comm, pure_eq_done, hv, decorate_error_eq_done, list.map_reverse,
             bind_eq_done, exists_eq_left, exists_and_distrib_left],
  -- We won't actually need the `val : ℕ` itself, since it is entirely characterized by the
  -- underlying characters. Instead, we will induct over the `list char` of characters from
  -- position `n` onwards, showing that if we could have provided a list at `n`, we could have
  -- provided a valid list of characters at `n + 1` too.
  clear hv val,
    /- We first prove some helper lemmas about the definition of `parser.nat`. Since it is defined
  in core, we have to work with how it is defined instead of changing its definition.
  In its definition, the function that folds over the parsed in digits is defined internally,
  as a lambda with anonymous destructor syntax, which leads to an unpleasant `nat._match_1` term
  when rewriting the definition of `parser.nat` away. Since we know exactly what the function is,
  we have a `rfl`-like lemma here to rewrite it back into a readable form.
  -/
  have natm : nat._match_1 = (λ (d : ℕ) p, ⟨p.1 + d * p.2, p.2 * 10⟩),
  { ext1, ext1 ⟨⟩, refl },
  -- We induct over the characters available at position `n` and onwards. Because `cb` is used
  -- in other expressions, we utilize the `induction H : ...` tactic to induct separately from
  -- destructing `cb` itself.
  induction H : (cb.to_list.drop n) with hd tl IH generalizing n,
  { -- Base case: there are no characters at position `n` or onwards, which means that
    -- `cb.size ≤ n`. But this is a contradiction, since we have `n < n' ≤ cb.size`.
    rw list.drop_eq_nil_iff_le at H,
    refine absurd ((lt_of_le_of_lt H hn).trans_le hn') _,
    simp },
  { -- Inductive case: we prove that if we could have parsed from `n + 1`, we could have also parsed
    -- from `n`, if there was a valid numerical character at `n`. Most of the body
    -- of this inductive case is generating the appropriate conditions for use of the inductive
    -- hypothesis.
    specialize @IH (n + 1),
    -- We have, by the inductive case, that there is at least one character `hd` at position `n`,
    -- with the rest at `tl`. We rearrange our inductive case to make `tl` be expressed as
    -- list.drop (n + 1), which fits out induction hypothesis conditions better. To use the
    -- rearranging lemma, we must prove that we are "dropping" in bounds, which we supply on-the-fly
    simp only [←list.cons_nth_le_drop_succ
      (show n < cb.to_list.length, by simpa using hn.trans_le hn')] at H,
    -- We prove that parsing our `n`th character, `hd`, would have resulted in a success from
    -- `parser.digit`, with the appropriate `ℕ` success value. We use this later to simplify the
    -- unwrapped fold, since `hd` is our head character.
    have hdigit : digit cb n = done (n + 1) (hd.to_nat - '0'.to_nat),
    { -- By our necessary condition, we know that `n` is in bounds, and that the `n`th character
      -- has the necessary "numeric" properties.
      specialize ho n hn (le_refl _),
      -- We prove an additional result that the conversion of `hd : char` to a `ℕ` would give a
      -- value `x ≤ 9`, since that is part of the iff statement in the `digit_eq_done` lemma.
      have : (buffer.read cb ⟨n, hn.trans_le hn'⟩).to_nat - '0'.to_nat ≤ 9,
      { -- We rewrite the statement to be a statement about characters instead, and split the
        -- inequality into the case that our hypotheses prove, and that `'0' ≤ '9'`, which
        -- is true by computation, handled by `dec_trivial`.
        rw [show 9 = '9'.to_nat - '0'.to_nat, from dec_trivial, tsub_le_tsub_iff_right],
        { exact ho.right },
        { dec_trivial } },
        -- We rely on the simplifier, mostly powered by `digit_eq_done`, and supply all the
        -- necessary conditions of bounds and identities about `hd`.
        simp [digit_eq_done, this, ←H.left, buffer.nth_le_to_list, hn.trans_le hn', ho] },
    -- We now case on whether we've moved to the end of our parse or not. We phrase this as
    -- casing on either `n + 1 < n` or `n ≤ n + 1`. The more difficult goal comes first.
    cases lt_or_ge (n + 1) n' with hn'' hn'',
    { -- Case `n + 1 < n'`. We can directly supply this to our induction hypothesis.
      -- We now have to prove, for the induction hypothesis, that the characters at positions `k`,
      -- `n + 1 ≤ k < n'` are "numeric". We already had this for `n ≤ k < n`, so we just rearrange
      -- the hypotheses we already have.
      specialize IH hn'' _ H.right,
      { intros k hk hk',
        apply ho,
        exact nat.le_of_succ_le hk' },
      -- With the induction hypothesis conditions satisfier, we can extract out a list that
      -- `parser.digit.many1` would have generated from position `n + 1`, as well as the associated
      -- property of the list, that it folds into what `nat.of_digits` generates from the
      -- characters in `cb : char_buffer`, now known as `hd :: tl`.
      obtain ⟨l, hdl, hvl⟩ := IH,
      -- Of course, the parsed in list from position `n` would be `l` prepended with the result
      -- of parsing in `hd`, which is provided explicitly.
      use (hd.to_nat - '0'.to_nat) :: l,
      -- We case on `l : list ℕ` so that we can make statements about the fold on `l`
      cases l with lhd ltl,
      { -- As before, if `l = []` then `many1` produced a `[]` success, which is a contradiction.
        simpa using hdl },
      -- Case `l = lhd :: ltl`. We can rewrite the fold of the function inside `parser.nat` on
      -- `lhd :: ltl`, which will be used to rewrite in the goal.
      simp only [natm, list.foldr] at hvl,
      -- We also expand the fold in the goal, using the expanded fold from our hypothesis, powered
      -- by `many1_eq_done` to proceed in the parsing. We know exactly what the next `many` will
      -- produce from `many1_eq_done_iff_many_eq_done.mp` of our `hdl` hypothesis. Finally,
      -- we also use `hdigit` to express what the single `parser.digit` result would be at `n`.
      simp only [natm, hvl, many1_eq_done, hdigit, many1_eq_done_iff_many_eq_done.mp hdl, true_and,
                 and_true, eq_self_iff_true, list.foldr, exists_eq_left'],
      -- Now our goal is solely about the equality of two different folding functions, one from the
      -- function defined inside `parser.nat` and the other as `nat.of_digits`, when applied to
      -- similar list inputs.
      -- First, we rid ourselves of `n'` by replacing with `n + m + 1`, which allows us to
      -- simplify the term of how many elements we are keeping using a `list.take`.
      obtain ⟨m, rfl⟩ : ∃ m, n' = n + m + 1 := nat.exists_eq_add_of_lt hn,
      -- The following rearrangement lemma is to simplify the `list.take (n' - n)` expression we had
      have : n + m + 1 - n = m + 1,
        { rw [add_assoc, tsub_eq_iff_eq_add_of_le, add_comm],
          exact nat.le_add_right _ _ },
      -- We also have to prove what is the `prod.snd` of the result of the fold of a `list (ℕ × ℕ)`
      -- with the function above. We use this lemma to finish our inductive case.
      have hpow : ∀ l, (list.foldr (λ (digit : ℕ) (x : ℕ × ℕ),
        (x.fst + digit * x.snd, x.snd * 10)) (0, 1) l).snd = 10 ^ l.length,
      { intro l,
        induction l with hd tl hl,
        { simp },
        { simp [hl, pow_succ, mul_comm] } },
      -- We prove that the parsed list of digits `(lhd :: ltl) : list ℕ` must be of length `m`
      -- which is used later when the `parser.nat` fold places `ltl.length` in the exponent.
      have hml : ltl.length + 1 = m := by simpa using many1_length_of_done hdl,
      -- A simplified `list.length (list.take ...)` expression refers to the minimum of the
      -- underlying length and the amount of elements taken. We know that `m ≤ tl.length`, so
      -- we provide this auxiliary lemma so that the simplified "take-length" can simplify further
      have ltll : min m tl.length = m,
      { -- On the way to proving this, we have to actually show that `m ≤ tl.length`, by showing
        -- that since `tl` was a subsequence in `cb`, and was retrieved from `n + 1` to `n + m + 1`,
        -- then since `n + m + 1 ≤ cb.size`, we have that `tl` must be at least `m` in length.
        simpa [←H.right, le_tsub_iff_right (hn''.trans_le hn').le, add_comm, add_assoc,
               add_left_comm] using hn' },
      -- Finally, we rely on the simplifier. We already expressions of `nat.of_digits` on both
      -- the LHS and RHS. All that is left to do is to prove that the summand on the LHS is produced
      -- by the fold of `nat.of_digits` on the RHS of `hd :: tl`. The `nat.of_digits_append` is used
      -- because of the append that forms from the included `list.reverse`. The lengths of the lists
      -- are placed in the exponents with `10` as a base, and are combined using `←pow_succ 10`.
      -- Any complicated expression about list lengths is further simplified by the auxiliary
      -- lemmas we just proved. Finally, we assist the simplifier by rearranging terms with our
      -- `n + m + 1 - n = m + 1` proof and `mul_comm`.
      simp [this, hpow, nat.of_digits_append, mul_comm, ←pow_succ 10, hml, ltll] },
    { -- Consider the case that `n' ≤ n + 1`. But then since `n < n' ≤ n + 1`, `n' = n + 1`.
      have : n' = n + 1 := le_antisymm hn'' (nat.succ_le_of_lt hn),
      subst this,
      -- This means we have only parsed in a single character, so the resulting parsed in list
      -- is explicitly formed from an expression we can construct from `hd`.
      use [[hd.to_nat - '0'.to_nat]],
      -- Our list expression simplifies nicely because it is a fold over a singleton, so we
      -- do not have to supply any auxiliary lemmas for it, other than what we already know about
      -- `hd` and the function defined in `parser.nat`. However, we will have to prove that our
      -- parse ended because of a good reason: either we are out of bounds or we hit a nonnumeric
      -- character.
      simp only [many1_eq_done, many_eq_done_nil, digit_eq_fail, natm, and.comm, and.left_comm,
                 hdigit, true_and, mul_one, nat.of_digits_singleton, list.take, exists_eq_left,
                 exists_and_distrib_right, add_tsub_cancel_left, eq_self_iff_true,
                 list.reverse_singleton, zero_add, list.foldr, list.map],
      -- We take the route of proving that we hit a nonnumeric character, since we already have
      -- a hypothesis that says that characters at `n'` and past it are nonnumeric. (Note, by now
      -- we have substituted `n + 1` for `n'.
      -- We are also asked to provide the error value that our failed parse would report. But
      -- `digit_eq_fail` already knows what it is, so we can discharge that with an inline `rfl`.
      refine ⟨_, or.inl ⟨rfl, _⟩⟩,
      -- The nonnumeric condition looks almost exactly like the hypothesis we already have, so
      -- we let the simplifier align them for us
      simpa using hb } }
end

end nat

end parser
