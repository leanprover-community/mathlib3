/- test cases for coinductive predicates -/
import data.stream.init
import meta.coinductive_predicates
universe u

coinductive all_stream {α : Type u} (s : set α) : stream α → Prop
| step : ∀{a : α} {ω : stream α}, a ∈ s → all_stream ω → all_stream (a :: ω)

example : Π {α : Type u}, set α → stream α → Prop :=
@all_stream
example : ∀ {α : Type u} {s : set α} {a : α} {ω : stream α}, a ∈ s → all_stream s ω →
  all_stream s (a :: ω) :=
@all_stream.step
example : ∀ {α : Type u} (s : set α) {a : stream α}, all_stream s a →
  all_stream.functional s (all_stream s) a :=
@all_stream.destruct
example : ∀ {α : Type u} (s : set α) (C : stream α → Prop) {a : stream α},
  C a →
  (∀ (a : stream α), C a → (∃ {a_1 : α} {ω : stream α}, a_1 ∈ s ∧ C ω ∧ a_1 :: ω = a)) →
  all_stream s a :=
@all_stream.corec_on
example : ∀ {α : Type u} (s : set α) (C : stream α → Prop),
    (∀ (a : stream α), C a → all_stream.functional s C a) →
      ∀ (a : stream α), C a → all_stream s a :=
@all_stream.corec_functional

coinductive all_stream' {α : Type u} (s : set α) : stream α → Prop
| step : ∀{ω : stream α}, stream.head ω ∈ s → all_stream' (stream.tail ω) → all_stream' ω

coinductive alt_stream : stream bool → Prop
| tt_step : ∀{ω : stream bool}, alt_stream (ff :: ω) → alt_stream (tt :: ff :: ω)
| ff_step : ∀{ω : stream bool}, alt_stream (tt :: ω) → alt_stream (ff :: tt :: ω)

example : stream bool → Prop := @alt_stream
example : ∀ {ω : stream bool}, alt_stream (ff :: ω) → alt_stream (tt :: ff :: ω) :=
@alt_stream.tt_step
example : ∀ {ω : stream bool}, alt_stream (tt :: ω) → alt_stream (ff :: tt :: ω) :=
@alt_stream.ff_step
example : ∀ (C : stream bool → Prop), (∀ (a : stream bool), C a → alt_stream.functional C a) →
  ∀ (a : stream bool), C a → alt_stream a :=
@alt_stream.corec_functional

mutual coinductive tt_stream, ff_stream
with tt_stream : stream bool → Prop
| step : ∀{ω : stream bool}, ff_stream ω → tt_stream (stream.cons tt ω)
with ff_stream : stream bool → Prop
| step : ∀{ω : stream bool}, tt_stream ω → ff_stream (stream.cons ff ω)

example : stream bool → Prop := @tt_stream
example : stream bool → Prop := @ff_stream
example : ∀ (C_tt_stream C_ff_stream : stream bool → Prop),
    (∀ (a : stream bool), C_tt_stream a → tt_stream.functional C_tt_stream C_ff_stream a) →
    (∀ (a : stream bool), C_ff_stream a → ff_stream.functional C_tt_stream C_ff_stream a) →
    ∀ (a : stream bool), C_tt_stream a → tt_stream a :=
@tt_stream.corec_functional
example : ∀ (C_tt_stream C_ff_stream : stream bool → Prop),
    (∀ (a : stream bool), C_tt_stream a → tt_stream.functional C_tt_stream C_ff_stream a) →
    (∀ (a : stream bool), C_ff_stream a → ff_stream.functional C_tt_stream C_ff_stream a) →
    ∀ (a : stream bool), C_ff_stream a → ff_stream a :=
@ff_stream.corec_functional

mutual coinductive tt_ff_stream, ff_tt_stream
with tt_ff_stream : stream bool → Prop
| step : ∀{ω : stream bool}, tt_ff_stream ω ∨ ff_tt_stream ω → tt_ff_stream (stream.cons tt ω)
with ff_tt_stream : stream bool → Prop
| step : ∀{ω : stream bool}, ff_tt_stream ω ∨ tt_ff_stream ω → ff_tt_stream (stream.cons ff ω)

inductive all_list {α : Type} (p : α → Prop) : list α → Prop
| nil  : all_list []
| cons : ∀a xs, p a → all_list xs → all_list (a :: xs)

@[monotonicity]
lemma monotonicity.all_list {α : Type} {p q : α → Prop} (h : ∀a, implies (p a) (q a)) :
  ∀xs, implies (all_list p xs) (all_list q xs)
| _ (all_list.nil)              := all_list.nil
| _ (all_list.cons a xs ha hxs) := all_list.cons _ _ (h a ha) (monotonicity.all_list _ hxs)

mutual coinductive walk_a, walk_b {α β : Type} (f : α → list β) (g : β → α) (p : α → Prop)
  (t : α → Prop)
with walk_a : α → Prop
| step : ∀a, all_list walk_b (f a) → p a → walk_a a
| term : ∀a, t a → walk_a a
with walk_b : β → Prop
| step : ∀b, walk_a (g b) → walk_b b

example : ∀ {α β : Type} (f : α → list β) (g : β → α) (p t C_walk_a : α → Prop)
  (C_walk_b : β → Prop) {a : α},
    C_walk_a a →
    (∀ (a : α), C_walk_a a → all_list C_walk_b (f a) ∧ p a ∨ t a) →
    (∀ (a : β), C_walk_b a → C_walk_a (g a)) → walk_a f g p t a :=
@walk_a.corec_on

coinductive walk_list {α : Type} (f : α → list α) (p : α → Prop) : ℕ → α → Prop
| step : ∀n a, all_list (walk_list n) (f a) → p a → walk_list (n + 1) a

example {f : ℕ → list ℕ} {a' : ℕ} {n : ℕ} {a : fin n} : true :=
begin
  suffices : walk_list f (λ a'', a'' = a') (n + 1) a', {trivial},
  coinduction walk_list.corec_on generalizing a n,
  show ∃ (n : ℕ),
    all_list (λ (a : ℕ), ∃ {n_1 : ℕ} {a_1 : fin n_1}, n_1 + 1 = n ∧ a' = a) (f a') ∧
      a' = a' ∧ n + 1 = w + 1,
  admit
end

coinductive coind_foo : list ℕ → Prop
| mk : ∀ xs, (∀ k l m, coind_foo (k::l::m::xs)) → coind_foo xs

meta example : true :=
begin
   success_if_fail { let := compact_relation },
   trivial
end

import_private compact_relation from tactic.coinduction

meta example : true :=
begin
  let := compact_relation,
  trivial
end
