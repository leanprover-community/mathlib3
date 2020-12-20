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
is always at a `parse_result.pos` that is at least `n`. Additionally, if the position `n` provided
was within the size of the `cb`, then the `parse_result.pos` of the output will also be within
the size of the `cb`.
-/
def valid : Prop :=
  ∀ (cb : char_buffer) (n : ℕ), n ≤ (p cb n).pos ∧ ((p cb n).pos ≤ cb.size → n ≤ cb.size)

lemma fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔
    ∃ (pos' : ℕ) (err : dlist string), p cb n = fail pos' err :=
begin
  cases p cb n,
  { simp only [not_not, exists_false, exists_eq_right', iff_false, exists_eq', not_forall] },
  { simp only [forall_const, ne.def, not_false_iff, exists_eq_right', exists_eq', forall_true_iff] }
end

lemma success_iff :
  (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
begin
  cases p cb n,
  { simp only [exists_eq_right', exists_eq', forall_const, ne.def, not_false_iff,
               forall_true_iff] },
  { simp only [exists_eq_right', exists_eq', exists_prop, not_not, exists_false, iff_false,
               not_forall] }
end

variables {p q cb n n' msgs msg}

lemma decorate_errors_fail (h : p cb n = fail n' err) :
  @decorate_errors α msgs p cb n = fail n ((dlist.lazy_of_list (msgs ()))) :=
begin
  dunfold decorate_errors,
  rw h,
  refl
end

lemma decorate_errors_success (h : p cb n = done n' a) :
  @decorate_errors α msgs p cb n = done n' a :=
begin
  dunfold decorate_errors,
  rw h,
  refl
end

lemma decorate_error_fail (h : p cb n = fail n' err) :
  @decorate_error α msg p cb n = fail n ((dlist.lazy_of_list ([msg ()]))) :=
decorate_errors_fail h

lemma decorate_error_success (h : p cb n = done n' a) :
  @decorate_error α msg p cb n = done n' a :=
decorate_errors_success h

@[simp] lemma decorate_errors_success_iff :
  @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
begin
  dunfold decorate_errors,
  cases p cb n,
  { rw decorate_errors },
  { rw decorate_errors,
    simp only }
end

@[simp] lemma decorate_error_success_iff :
  @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
decorate_errors_success_iff

@[simp] lemma decorate_errors_failure_iff :
  @decorate_errors α msgs p cb n = fail n err ↔
    err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
begin
  dunfold decorate_errors,
  cases p cb n,
  { rw decorate_errors,
    simp only [exists_false, and_false] },
  { rw decorate_errors,
    simp only [true_and, and_true, eq_self_iff_true, exists_eq_right', exists_eq', eq_comm] }
end

@[simp] lemma decorate_error_failure_iff :
  @decorate_error α msg p cb n = fail n err ↔
    err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
decorate_errors_failure_iff

@[simp] lemma return_eq_pure : (@return parser _ _ a) = pure a := rfl

@[simp] lemma pure_eq_done : (@pure parser _ _ a) = λ _ n, done n a := rfl

section bind

variable {f : α → parser β}

@[simp] lemma bind_eq_bind : p.bind f = p >>= f := rfl

@[simp] lemma bind_eq_done :
  (p >>= f) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = done n' b :=
begin
  split,
  { intro h,
    simp_rw [←bind_eq_bind, parser.bind] at h,
    cases p cb n with pos r pos err,
    { refine ⟨pos, r, rfl, _⟩,
      rw ←h,
      refl },
    { simpa only using h } },
  { rintro ⟨r, pos, h⟩,
    simp only [h, ←bind_eq_bind, parser.bind, eq_self_iff_true, and_self] }
end

@[simp] lemma bind_eq_fail :
  (p >>= f) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = fail n' err)
  :=
begin
  split,
  { intro h,
    simp_rw [←bind_eq_bind, parser.bind] at h,
    cases p cb n with pos r pos err,
    { rw ←h,
      simp only [false_or, exists_false],
      refine ⟨pos, r, by simp only [eq_self_iff_true, and_self], _⟩,
      refl },
    { simpa only [parser.bind, exists_false, or_false, false_and] using h } },
  { rintro (h | ⟨r, n', h, h'⟩),
    { simp only [←bind_eq_bind, parser.bind, h, eq_self_iff_true, and_self] },
    { simp only [←h', ←bind_eq_bind, parser.bind, h] } }
end

@[simp] lemma and_then_eq_bind {α β : Type} {m : Type → Type} [monad m] (a : m α) (b : m β) :
  a >> b = a >>= (λ _, b) := rfl

lemma and_then_fail :
  (p >> return ()) cb n = parse_result.fail n' err ↔ p cb n = fail n' err :=
by simp only [and_then_eq_bind, return_eq_pure, exists_false, or_false, pure_eq_done,
              bind_eq_fail, and_false]

lemma and_then_success :
  (p >> return ()) cb n = parse_result.done n' () ↔ ∃ a, p cb n = done n' a:=
by simp only [pure_eq_done, and_then_eq_bind, and_true, bind_eq_done, exists_eq_right,
              eq_iff_true_of_subsingleton, return_eq_pure, exists_and_distrib_right]

end bind

section map

variable {f : α → β}

@[simp] lemma map_eq_done : (f <$> p) cb n = done n' b ↔
  ∃ (a : α), p cb n = done n' a ∧ f a = b :=
begin
  rw ←is_lawful_monad.bind_pure_comp_eq_map,
  simp only [bind_eq_done, function.comp_app, pure_eq_done],
  split,
  { rintro ⟨np, a, h, rfl, rfl⟩,
    exact ⟨a, h, rfl⟩ },
  { rintro ⟨a, h, rfl⟩,
    exact ⟨n', a, h, rfl, rfl⟩ }
end

@[simp] lemma map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp only [←bind_pure_comp_eq_map, exists_false, function.comp_app, or_false, pure_eq_done,
              bind_eq_fail, and_false]

end map

@[simp] lemma orelse_eq_orelse : p.orelse q = (p <|> q) := rfl

@[simp] lemma orelse_eq_done : (p <|> q) cb n = done n' a ↔
  (p cb n = done n' a ∨ (q cb n = done n' a ∧ ∃ err, p cb n = fail n err)) :=
begin
  rw ←orelse_eq_orelse,
  split,
  { intro h,
    simp_rw parser.orelse at h,
    cases p cb n with posp resp posp errp,
    { left,
      simpa only [parser.orelse] using h },
    { right,
      simp only [parser.orelse, ite_not] at h,
      split_ifs at h with H H,
      { cases q cb n with posq resq posq errq,
        { simp only [parser.orelse] at h,
          simp only [true_and, exists_eq', H, eq_self_iff_true, h] },
        { simp only [parser.orelse] at h,
          split_ifs at h;
          exact h.elim } },
      { exact h.elim } } },
  { rintro (h | ⟨h', err, h⟩),
    { simp only [parser.orelse, h, eq_self_iff_true, and_self] },
    { simp only [h, parser.orelse, eq_self_iff_true, not_true, if_false, ne.def],
      cases q cb n with posq resq posq errq,
      { simpa only [parser.orelse] using h' },
      { simpa only using h' } } }
end

@[simp] lemma orelse_eq_fail_eq : (p <|> q) cb n = fail n err ↔
  (p cb n = fail n err ∧ ∃ (nq errq), n < nq ∧ q cb n = fail nq errq) ∨
  (∃ (errp errq), p cb n = fail n errp ∧ q cb n = fail n errq ∧ errp ++ errq = err)
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp only [parser.orelse, exists_false, false_and, or_self] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def,
               exists_eq_left'],
    cases q cb n with posq resq posq errq,
    { simp only [parser.orelse, exists_false, and_false, false_and, or_self] },
    { simp only [parser.orelse, exists_eq_right'],
      split_ifs with H H',
      { simp only [H, true_and, and_true, eq_self_iff_true, ne_of_gt H, exists_false, or_false,
                   false_and] },
      { have hn : posq ≠ n := ne_of_lt H',
        have hl : posq ≤ n := le_of_not_lt H,
        simp only [hn, hl, false_iff, not_and, not_lt, exists_false, or_false, false_and,
                   forall_true_iff] },
      { have : posq = n := le_antisymm (le_of_not_lt H) (le_of_not_lt H'),
        simp only [this, lt_irrefl, true_and, false_or, eq_self_iff_true, exists_eq_left',
                   and_false] } } },
  { simp only [h, parser.orelse, if_true, exists_false, ne.def, not_false_iff, false_and,
               or_self] },
end

lemma orelse_eq_fail_invalid_lt (hn : n' < n) : (p <|> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨
  (q cb n = fail n' err ∧ (∃ (errp), p cb n = fail n errp))
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp only [parser.orelse, exists_false, or_self, and_false] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def, and_true,
               false_or, exists_eq', false_and, ne_of_gt hn],
    cases q cb n with posq resq posq errq,
    { simp only [parser.orelse, not_false_iff] },
    { simp only [parser.orelse],
      split_ifs with H H',
      { have : posq ≠ n' := ne_of_gt (lt_trans hn H),
        simp only [false_and, ne_of_gt hn, this] },
      { simp only [iff_self] },
      { have : posq = n := le_antisymm (le_of_not_lt H) (le_of_not_lt H'),
        simp only [ne_of_gt hn, this, false_and] } } },
  { simp only [h, parser.orelse, if_true, exists_false, ne.def, not_false_iff, false_and,
               or_false, and_false] },
end

lemma orelse_eq_fail_of_valid_ne (hq : q.valid) (hn : n ≠ n') :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err
 :=
begin
  rw ←orelse_eq_orelse,
  simp only [parser.orelse, exists_and_distrib_left],
  cases p cb n with posp resp posp errp,
  { simp [parser.orelse, exists_false, or_self, and_false] },
  by_cases h : posp = n,
  { simp only [h, parser.orelse, true_and, eq_self_iff_true, not_true, if_false, ne.def,
               hn, and_true, false_or, exists_eq', false_and],
    specialize hq cb n,
    cases q cb n with posq resq posq errq,
    { simp [parser.orelse] },
    { simp only [parser.orelse, if_false],
      simp only [parse_result.pos] at hq,
      rcases eq_or_lt_of_le hq.left with rfl|H,
      { simp only [lt_irrefl, hn, if_false, false_and] },
      { simp only [H, if_true, hn, false_and] } } },
  { simp only [h, parser.orelse, if_true, ne.def, not_false_iff] },
end

@[simp] lemma parser_eq_parser : @parser.failure α = failure := rfl

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
  specialize hp cb n,
  cases hx : (p >>= f) cb n,
  { obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx,
    specialize hf a cb n',
    simp only [h', parse_result.pos] at hf,
    simp only [h, parse_result.pos] at hp,
    simp only [parse_result.pos],
    split,
    { exact le_trans hp.left hf.left },
    { intro hn,
      simp [hn, hf, hp] } },
  { obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx,
    { simpa only [h] using hp },
    { specialize hf a cb n',
      simp only [h', parse_result.pos] at hf,
      simp only [h, parse_result.pos] at hp,
      simp only [parse_result.pos],
      split,
      { exact le_trans hp.left hf.left },
      { intro hn,
        simp only [hn, hf, hp] } } },
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
  { refine and_then (h _ (list.mem_cons_self _ _))
      (hl (λ _ ha, h _ (list.mem_cons_of_mem _ ha))) }
end

@[simp] lemma failure : @parser.valid α failure :=
begin
  simp only [failure_def, valid, imp_self, and_true, parse_result.pos],
  rintro - _,
  refl
end

@[simp] lemma guard {p : Prop} [decidable p] : valid (guard p) :=
by simp only [guard, apply_ite valid, pure, failure, or_true, if_true_left_eq_or]

@[simp] lemma orelse (hp : p.valid) (hq : q.valid) : (p <|> q).valid :=
begin
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h', err, h⟩ := orelse_eq_done.mp hx,
    { simpa only [h] using hp cb n },
    { simpa only [h'] using hq cb n } },
  { by_cases h : n = posx,
    { simp only [hx, h, imp_self, and_true, parse_result.pos] },
    { rw orelse_eq_fail_of_valid_ne hq h at hx,
      simpa only [parse_result.pos, hx] using hp cb n } }
end

@[simp] lemma decorate_errors (hp : p.valid) :
  (@decorate_errors α msgs p).valid :=
begin
  dunfold decorate_errors,
  intros cb n,
  specialize hp cb n,
  dsimp only,
  cases p cb n,
  { simpa only using hp },
  { simp only [decorate_errors, imp_self, and_true, parse_result.pos] },
end

@[simp] lemma decorate_error (hp : p.valid) : (@decorate_error α msg p).valid :=
decorate_errors hp

@[simp] lemma any_char : valid any_char :=
begin
  intros cb n,
  simp only [any_char],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le},
  { simp only [imp_self, and_true, parse_result.pos] }
end

@[simp] lemma sat {p : char → Prop} [decidable_pred p] : valid (sat p) :=
begin
  intros cb n,
  simp only [sat],
  split_ifs,
  { simpa only [true_and, zero_le, le_add_iff_nonneg_right,
                parse_result.pos] using nat.le_of_succ_le },
  { simp only [imp_self, and_true, parse_result.pos] },
  { simp only [parse_result.pos, imp_self, and_true] }
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
