/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.hint

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well known
`G4ip` algorithm:
[Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*][dyckhoff_1992].

All built in propositional connectives are supported: `true`, `false`, `and`, `or`, `implies`,
`not`, `iff`, `xor`, as well as `eq` and `ne` on propositions. Anything else, including definitions
and predicate logical connectives (`forall` and `exists`), are not supported, and will have to be
simplified or instantiated before calling this tactic.

The resulting proofs will never use any axioms except possibly `propext`, and `propext` is only
used if the input formula contains an equality of propositions `p = q`.

## Implementation notes

The core logic of the prover is in three functions:

* `prove : context → prop → state_t ℕ option proof`: The main entry point.
  Gets a context and a goal, and returns a `proof` object or fails, using `state_t ℕ` for the name
  generator.
* `search : context → prop → state_t ℕ option proof`: Same meaning as `proof`, called during the
  search phase (see below).
* `context.add : prop → proof → context → except (prop → proof) context`: Adds a proposition with
  its proof into the context, but it also does some simplifications on the spot while doing so.
  It will either return the new context, or if it happens to notice a proof of false, it will
  return a function to compute a proof of any proposition in the original context.

The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`.
  * `context.add`:
    * simplify `Γ, ⊤ ⊢ B` to `Γ ⊢ B`
    * `Γ, ⊥ ⊢ B` is true
    * simplify `Γ, A ∧ B ⊢ C` to `Γ, A, B ⊢ C`
    * simplify `Γ, ⊥ → A ⊢ B` to `Γ ⊢ B`
    * simplify `Γ, ⊤ → A ⊢ B` to `Γ, A ⊢ B`
    * simplify `Γ, A ∧ B → C ⊢ D` to `Γ, A → B → C ⊢ D`
    * simplify `Γ, A ∨ B → C ⊢ D` to `Γ, A → C, B → C ⊢ D`
  * `prove`:
    * `Γ ⊢ ⊤` is true
    * simplify `Γ ⊢ A → B` to `Γ, A ⊢ B`
  * `search`:
    * `Γ, P ⊢ P` is true
    * simplify `Γ, P, P → A ⊢ B` to `Γ, P, A ⊢ B`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
  * simplify `Γ ⊢ A ∧ B` to `Γ ⊢ A` and `Γ ⊢ B`
  * simplify `Γ, A ∨ B ⊢ C` to `Γ, A ⊢ C` and `Γ, B ⊢ C`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ A`
  * `Γ ⊢ A ∨ B` follows from `Γ ⊢ B`
  * `Γ, (A₁ → A₂) → C ⊢ B` follows from `Γ, A₂ → C, A₁ ⊢ A₂` and `Γ, C ⊢ B`

This covers the core algorithm, which only handles `true`, `false`, `and`, `or`, and `implies`.
For `iff` and `eq`, we treat them essentially the same as `(p → q) ∧ (q → p)`, although we use
a different `prop` representation because we have to remember to apply different theorems during
replay. For definitions like `not` and `xor`, we just eagerly unfold them. (This could potentially
cause a blowup issue for `xor`, but it isn't used very often anyway. We could add it to the `prop`
grammar if it matters.)

## Tags

propositional logic, intuitionistic logic, decision procedure
-/

namespace tactic
namespace itauto

/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/
@[derive [has_reflect, decidable_eq]]
inductive and_kind | and | iff | eq

instance : inhabited and_kind := ⟨and_kind.and⟩

/-- A reified inductive type for propositional logic. -/
@[derive [has_reflect, decidable_eq]]
inductive prop : Type
| var : ℕ → prop            -- propositional atoms P_i
| true : prop               -- ⊤
| false : prop              -- ⊥
| and' : and_kind → prop → prop → prop  -- p ∧ q, p ↔ q, p = q
| or : prop → prop → prop   -- p ∨ q
| imp : prop → prop → prop  -- p → q

/-- Constructor for `p ∧ q`. -/
@[pattern] def prop.and : prop → prop → prop := prop.and' and_kind.and
/-- Constructor for `p ↔ q`. -/
@[pattern] def prop.iff : prop → prop → prop := prop.and' and_kind.iff
/-- Constructor for `p = q`. -/
@[pattern] def prop.eq : prop → prop → prop := prop.and' and_kind.eq
/-- Constructor for `¬ p`. -/
@[pattern] def prop.not (a : prop) : prop := a.imp prop.false
/-- Constructor for `xor p q`. -/
@[pattern] def prop.xor (a b : prop) : prop := (a.and b.not).or (b.and a.not)

instance : inhabited prop := ⟨prop.true⟩

/-- Given the contents of an `and` variant, return the two conjuncts. -/
def and_kind.sides : and_kind → prop → prop → prop × prop
| and_kind.and A B := (A, B)
| _ A B := (A.imp B, B.imp A)

/-- Debugging printer for propositions. -/
meta def prop.to_format : prop → format
| (prop.var i) := format!"v{i}"
| prop.true := format!"⊤"
| prop.false := format!"⊥"
| (prop.and p q) := format!"({p.to_format} ∧ {q.to_format})"
| (prop.iff p q) := format!"({p.to_format} ↔ {q.to_format})"
| (prop.eq p q) := format!"({p.to_format} = {q.to_format})"
| (prop.or p q) := format!"({p.to_format} ∨ {q.to_format})"
| (prop.imp p q) := format!"({p.to_format} → {q.to_format})"

meta instance : has_to_format prop := ⟨prop.to_format⟩

section
open ordering

/-- A comparator for `and_kind`. (There should really be a derive handler for this.) -/
def and_kind.cmp (p q : and_kind) : ordering :=
by { cases p; cases q, exacts [eq, lt, lt, gt, eq, lt, gt, gt, eq] }

/-- A comparator for propositions. (There should really be a derive handler for this.) -/
def prop.cmp (p q : prop) : ordering :=
begin
  induction p with _ ap _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ generalizing q; cases q,
  case var var { exact cmp p q },
  case true true { exact eq },
  case false false { exact eq },
  case and' and' : aq q₁ q₂ { exact (ap.cmp aq).or_else ((p₁ q₁).or_else (p₂ q₂)) },
  case or or : q₁ q₂ { exact (p₁ q₁).or_else (p₂ q₂) },
  case imp imp : q₁ q₂ { exact (p₁ q₁).or_else (p₂ q₂) },
  exacts [lt, lt, lt, lt, lt,
          gt, lt, lt, lt, lt,
          gt, gt, lt, lt, lt,
          gt, gt, gt, lt, lt,
          gt, gt, gt, gt, lt,
          gt, gt, gt, gt, gt]
end

instance : has_lt prop := ⟨λ p q, p.cmp q = lt⟩

instance : decidable_rel (@has_lt.lt prop _) := λ _ _, ordering.decidable_eq _ _

end

/-- A reified inductive proof type for intuitionistic propositional logic. -/
@[derive has_reflect]
inductive proof
-- ⊢ A, causes failure during reconstruction
| «sorry» : proof
-- (n: A) ⊢ A
| hyp (n : name) : proof
-- ⊢ ⊤
| triv : proof
-- (p: ⊥) ⊢ A
| exfalso' (p : proof) : proof
-- (p: (x: A) ⊢ B) ⊢ A → B
| intro (x : name) (p : proof) : proof
-- ak = and:  (p: A ∧ B) ⊢ A
-- ak = iff:  (p: A ↔ B) ⊢ A → B
-- ak = eq:  (p: A = B) ⊢ A → B
| and_left (ak : and_kind) (p : proof) : proof
-- ak = and:  (p: A ∧ B) ⊢ B
-- ak = iff:  (p: A ↔ B) ⊢ B → A
-- ak = eq:  (p: A = B) ⊢ B → A
| and_right (ak : and_kind) (p : proof) : proof
-- ak = and:  (p₁: A) (p₂: B) ⊢ A ∧ B
-- ak = iff:  (p₁: A → B) (p₁: B → A) ⊢ A ↔ B
-- ak = eq:  (p₁: A → B) (p₁: B → A) ⊢ A = B
| and_intro (ak : and_kind) (p₁ p₂ : proof) : proof
-- ak = and:  (p: A ∧ B → C) ⊢ A → B → C
-- ak = iff:  (p: (A ↔ B) → C) ⊢ (A → B) → (B → A) → C
-- ak = eq:  (p: (A = B) → C) ⊢ (A → B) → (B → A) → C
| curry (ak : and_kind) (p : proof) : proof
-- This is a partial application of curry.
-- ak = and:  (p: A ∧ B → C) (q : A) ⊢ B → C
-- ak = iff:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C
-- ak = eq:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C
| curry₂ (ak : and_kind) (p q : proof) : proof
-- (p: A → B) (q: A) ⊢ B
| app' : proof → proof → proof
-- (p: A ∨ B → C) ⊢ A → C
| or_imp_left (p : proof) : proof
-- (p: A ∨ B → C) ⊢ B → C
| or_imp_right (p : proof) : proof
-- (p: A) ⊢ A ∨ B
| or_inl (p : proof) : proof
-- (p: B) ⊢ A ∨ B
| or_inr (p : proof) : proof
-- (p: B) ⊢ A ∨ B
-- (p₁: A ∨ B) (p₂: (x: A) ⊢ C) (p₃: (x: B) ⊢ C) ⊢ C
| or_elim' (p₁ : proof) (x : name) (p₂ p₃ : proof) : proof
-- (p₁: decidable A) (p₂: (x: A) ⊢ C) (p₃: (x: ¬ A) ⊢ C) ⊢ C
| decidable_elim (classical : bool) (p₁ x : name) (p₂ p₃ : proof) : proof
-- classical = ff: (p: decidable A) ⊢ A ∨ ¬A
-- classical = tt: (p: Prop) ⊢ p ∨ ¬p
| em (classical : bool) (p : name) : proof
-- The variable x here names the variable that will be used in the elaborated proof
-- (p: ((x:A) → B) → C) ⊢ B → C
| imp_imp_simp (x : name) (p : proof) : proof

instance : inhabited proof := ⟨proof.triv⟩

/-- Debugging printer for proof objects. -/
meta def proof.to_format : proof → format
| proof.sorry := "sorry"
| (proof.hyp i) := to_fmt i
| proof.triv := "triv"
| (proof.exfalso' p) := format!"(exfalso {p.to_format})"
| (proof.intro x p) := format!"(λ {x}, {p.to_format})"
| (proof.and_left _ p) := format!"{p.to_format} .1"
| (proof.and_right _ p) := format!"{p.to_format} .2"
| (proof.and_intro _ p q) := format!"⟨{p.to_format}, {q.to_format}⟩"
| (proof.curry _ p) := format!"(curry {p.to_format})"
| (proof.curry₂ _ p q) := format!"(curry {p.to_format} {q.to_format})"
| (proof.app' p q) := format!"({p.to_format} {q.to_format})"
| (proof.or_imp_left p) := format!"(or_imp_left {p.to_format})"
| (proof.or_imp_right p) := format!"(or_imp_right {p.to_format})"
| (proof.or_inl p) := format!"(or.inl {p.to_format})"
| (proof.or_inr p) := format!"(or.inr {p.to_format})"
| (proof.or_elim' p x q r) :=
  format!"({p.to_format}.elim (λ {x}, {q.to_format}) (λ {x}, {r.to_format})"
| (proof.em ff p) := format!"(decidable.em {p})"
| (proof.em tt p) := format!"(classical.em {p})"
| (proof.decidable_elim _ p x q r) :=
  format!"({p}.elim (λ {x}, {q.to_format}) (λ {x}, {r.to_format})"
| (proof.imp_imp_simp _ p) := format!"(imp_imp_simp {p.to_format})"

meta instance : has_to_format proof := ⟨proof.to_format⟩

/-- A variant on `proof.exfalso'` that performs opportunistic simplification. -/
meta def proof.exfalso : prop → proof → proof
| prop.false p := p
| A p := proof.exfalso' p

/-- A variant on `proof.or_elim` that performs opportunistic simplification. -/
meta def proof.or_elim : proof → name → proof → proof → proof
| (proof.em cl p) x q r := proof.decidable_elim cl p x q r
| p x q r := proof.or_elim' p x q r

/-- A variant on `proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
meta def proof.app : proof → proof → proof
| (proof.curry ak p) q := proof.curry₂ ak p q
| (proof.curry₂ ak p q) r := p.app (q.and_intro ak r)
| (proof.or_imp_left p) q := p.app q.or_inl
| (proof.or_imp_right p) q := p.app q.or_inr
| (proof.imp_imp_simp x p) q := p.app (proof.intro x q)
| p q := p.app' q

-- Note(Mario): the typechecker is disabled because it requires proofs to carry around additional
-- props. These can be retrieved from the git history if you want to re-enable this.
/-
/-- A typechecker for the `proof` type. This is not used by the tactic but can be used for
debugging. -/
meta def proof.check : name_map prop → proof → option prop
| Γ (proof.hyp i) := Γ.find i
| Γ proof.triv := some prop.true
| Γ (proof.exfalso' A p) := guard (p.check Γ = some prop.false) $> A
| Γ (proof.intro x A p) := do B ← p.check (Γ.insert x A), pure (prop.imp A B)
| Γ (proof.and_left ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).1
| Γ (proof.and_right ak p) := do
  prop.and' ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).2
| Γ (proof.and_intro and_kind.and p q) := do
  A ← p.check Γ, B ← q.check Γ,
  pure (A.and B)
| Γ (proof.and_intro ak p q) := do
  prop.imp A B ← p.check Γ | none,
  C ← q.check Γ, guard (C = prop.imp B A) $> (A.and' ak B)
| Γ (proof.curry ak p) := do
  prop.imp (prop.and' ak' A B) C ← p.check Γ | none,
  let (A', B') := ak.sides A B,
  guard (ak = ak') $> (A'.imp $ B'.imp C)
| Γ (proof.curry₂ ak p q) := do
  prop.imp (prop.and' ak' A B) C ← p.check Γ | none,
  A₂ ← q.check Γ,
  let (A', B') := ak.sides A B,
  guard (ak = ak' ∧ A₂ = A') $> (B'.imp C)
| Γ (proof.app' p q) := do prop.imp A B ← p.check Γ | none, A' ← q.check Γ, guard (A = A') $> B
| Γ (proof.or_imp_left B p) := do
  prop.imp (prop.or A B') C ← p.check Γ | none,
  guard (B = B') $> (A.imp C)
| Γ (proof.or_imp_right A p) := do
  prop.imp (prop.or A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
| Γ (proof.or_inl B p) := do A ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_inr A p) := do B ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_elim p x q r) := do
  prop.or A B ← p.check Γ | none,
  C ← q.check (Γ.insert x A),
  C' ← r.check (Γ.insert x B),
  guard (C = C') $> C
| Γ (proof.imp_imp_simp x A p) := do
  prop.imp (prop.imp A' B) C ← p.check Γ | none,
  guard (A = A') $> (B.imp C)
-/

/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline] meta def fresh_name : ℕ → name × ℕ :=
λ n, (mk_simple_name ("h" ++ to_string n), n+1)

/-- The context during proof search is a map from propositions to proof values. -/
meta def context := native.rb_map prop proof

/-- Debug printer for the context. -/
meta def context.to_format (Γ : context) : format :=
Γ.fold "" $ λ P p f, P.to_format /- ++ " := " ++ p.to_format -/ ++ ",\n" ++ f

meta instance : has_to_format context := ⟨context.to_format⟩

/-- Insert a proposition and its proof into the context, as in `have : A := p`. This will eagerly
apply all level 1 rules on the spot, which are rules that don't split the goal and are validity
preserving: specifically, we drop `⊤` and `A → ⊤` hypotheses, close the goal if we find a `⊥`
hypothesis, split all conjunctions, and also simplify `⊥ → A` (drop), `⊤ → A` (simplify to `A`),
`A ∧ B → C` (curry to `A → B → C`) and `A ∨ B → C` (rewrite to `(A → C) ∧ (B → C)` and split). -/
meta def context.add : prop → proof → context → except (prop → proof) context
| prop.true p Γ := pure Γ
| prop.false p Γ := except.error (λ A, proof.exfalso A p)
| (prop.and' ak A B) p Γ := do
  let (A, B) := ak.sides A B,
  Γ ← Γ.add A (p.and_left ak),
  Γ.add B (p.and_right ak)
| (prop.imp prop.false A) p Γ := pure Γ
| (prop.imp prop.true A) p Γ := Γ.add A (p.app proof.triv)
| (prop.imp (prop.and' ak A B) C) p Γ :=
  let (A, B) := ak.sides A B in
  Γ.add (prop.imp A (B.imp C)) (p.curry ak)
| (prop.imp (prop.or A B) C) p Γ := do
  Γ ← Γ.add (A.imp C) p.or_imp_left,
  Γ.add (B.imp C) p.or_imp_right
| (prop.imp A prop.true) p Γ := pure Γ
| A p Γ := pure (Γ.insert A p)

/-- Add `A` to the context `Γ` with proof `p`. This version of `context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline] meta def context.with_add (Γ : context) (A : prop) (p : proof)
  (B : prop) (f : context → prop → ℕ → bool × proof × ℕ) (n : ℕ) : bool × proof × ℕ :=
match Γ.add A p with
| except.ok Γ_A := f Γ_A B n
| except.error p := (tt, p B, n)
end

/-- Map a function over the proof (regardless of whether the proof is successful or not). -/
def map_proof (f : proof → proof) : bool × proof × ℕ → bool × proof × ℕ
| (b, p, n) := (b, f p, n)

/-- Convert a value-with-success to an optional value. -/
def is_ok {α} : bool × α → option α
| (ff, p) := none
| (tt, p) := some p

/-- Skip the continuation and return a failed proof if the boolean is false. -/
def when_ok : bool → (ℕ → bool × proof × ℕ) → ℕ → bool × proof × ℕ
| ff f n := (ff, proof.sorry, n)
| tt f n := f n

/-- The search phase, which deals with the level 3 rules, which are rules that are not validity
preserving and so require proof search. One obvious one is the or-introduction rule: we prove
`A ∨ B` by proving `A` or `B`, and we might have to try one and backtrack.

There are two rules dealing with implication in this category: `p, p → C ⊢ B` where `p` is an
atom (which is safe if we can find it but often requires the right search to expose the `p`
assumption), and `(A₁ → A₂) → C ⊢ B`. We decompose the double implication into two subgoals: one to
prove `A₁ → A₂`, which can be written `A₂ → C, A₁ ⊢ A₂` (where we used `A₁` to simplify
`(A₁ → A₂) → C`), and one to use the consequent, `C ⊢ B`. The search here is that there are
potentially many implications to split like this, and we have to try all of them if we want to be
complete. -/
meta def search (prove : context → prop → ℕ → bool × proof × ℕ) :
  context → prop → ℕ → bool × proof × ℕ
| Γ B n := match Γ.find B with
  | some p := (tt, p, n)
  | none :=
    let search₁ := Γ.fold none $ λ A p r, match r with
    | some r := some r
    | none := match A with
      | prop.imp A' C := match Γ.find A' with
        | some q := is_ok $ context.with_add (Γ.erase A) C (p.app q) B prove n
        | none := match A' with
          | prop.imp A₁ A₂ := do
            let Γ : context := Γ.erase A,
            let (a, n) := fresh_name n,
            (p₁, n) ← is_ok $ Γ.with_add A₁ (proof.hyp a) A₂ (λ Γ_A₁ A₂,
              Γ_A₁.with_add (prop.imp A₂ C) (proof.imp_imp_simp a p) A₂ prove) n,
            is_ok $ Γ.with_add C (p.app (proof.intro a p₁)) B prove n
          | _ := none
          end
        end
      | _ := none
      end
    end in
    match search₁ with
    | some r := (tt, r)
    | none := match B with
      | prop.or B₁ B₂ := match map_proof proof.or_inl (prove Γ B₁ n) with
        | (ff, _) := map_proof proof.or_inr (prove Γ B₂ n)
        | r := r
        end
      | _ := (ff, proof.sorry, n)
      end
    end
  end

/-- The main prover. This receives a context of proven or assumed lemmas and a target proposition,
and returns a proof or `none` (with state for the fresh variable generator).
The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`

The level 1 rules on the right of the turnstile are `Γ ⊢ ⊤` and `Γ ⊢ A → B`, these are easy to
handle. The rule `Γ ⊢ A ∧ B` is a level 2 rule, also handled here. If none of these apply, we try
the level 2 rule `A ∨ B ⊢ C` by searching the context and splitting all ors we find. Finally, if
we don't make any more progress, we go to the search phase.
-/
meta def prove : context → prop → ℕ → bool × proof × ℕ
| Γ prop.true n := (tt, proof.triv, n)
| Γ (prop.imp A B) n :=
  let (a, n) := fresh_name n in
  map_proof (proof.intro a) $ Γ.with_add A (proof.hyp a) B prove n
| Γ (prop.and' ak A B) n :=
  let (A, B) := ak.sides A B in
  let (b, p, n) := prove Γ A n in
  map_proof (p.and_intro ak) $ when_ok b (prove Γ B) n
| Γ B n := Γ.fold (λ b Γ, cond b prove (search prove) Γ B) (λ A p IH b Γ n,
    match A with
    | prop.or A₁ A₂ :=
      let Γ : context := Γ.erase A in
      let (a, n) := fresh_name n in
      let (b, p₁, n) := Γ.with_add A₁ (proof.hyp a) B (λ Γ _, IH tt Γ) n in
      map_proof (proof.or_elim p a p₁) $
        when_ok b (Γ.with_add A₂ (proof.hyp a) B (λ Γ _, IH tt Γ)) n
    | _ := IH b Γ n
    end) ff Γ n

/-- Reifies an atomic or otherwise unrecognized proposition. If it is defeq to a proposition we
have already allocated, we reuse it, otherwise we name it with a new index. -/
meta def reify_atom (atoms : ref (buffer expr)) (e : expr) : tactic prop := do
  vec ← read_ref atoms,
  o ← try_core $ vec.iterate failure (λ i e' r,
    r <|> (is_def_eq e e' >> pure i.1)),
  match o with
  | none := write_ref atoms (vec.push_back e) $> prop.var vec.size
  | some i := pure $ prop.var i
  end

/-- Reify an `expr` into a `prop`, allocating anything non-propositional as an atom in the
`atoms` list. -/
meta def reify (atoms : ref (buffer expr)) : expr → tactic prop
| `(true) := pure prop.true
| `(false) := pure prop.false
| `(¬ %%a) := prop.not <$> reify a
| `(%%a ∧ %%b) := prop.and <$> reify a <*> reify b
| `(%%a ∨ %%b) := prop.or <$> reify a <*> reify b
| `(%%a ↔ %%b) := prop.iff <$> reify a <*> reify b
| `(xor %%a %%b) := prop.xor <$> reify a <*> reify b
| `(@eq Prop %%a %%b) := prop.eq <$> reify a <*> reify b
| `(@ne Prop %%a %%b) := prop.not <$> (prop.eq <$> reify a <*> reify b)
| `(implies %%a %%b) := prop.imp <$> reify a <*> reify b
| e@`(%%a → %%b) :=
  if b.has_var then reify_atom atoms e else prop.imp <$> reify a <*> reify b
| e := reify_atom atoms e

/-- Once we have a proof object, we have to apply it to the goal. (Some of these cases are a bit
annoying because `applyc` gets the arguments wrong sometimes so we have to use `to_expr` instead.)
-/
meta def apply_proof : name_map expr → proof → tactic unit
| Γ proof.sorry := fail "itauto failed"
| Γ (proof.hyp n) := do e ← Γ.find n, exact e
| Γ proof.triv := triv
| Γ (proof.exfalso' p) := do
  t ← mk_mvar, to_expr ``(false.elim %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.intro x p) := do e ← intro_core x, apply_proof (Γ.insert x e) p
| Γ (proof.and_left and_kind.and p) := do
  t ← mk_mvar, to_expr ``(and.left %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_left and_kind.iff p) := do
  t ← mk_mvar, to_expr ``(iff.mp %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_left and_kind.eq p) := do
  t ← mk_mvar, to_expr ``(cast %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.and p) := do
  t ← mk_mvar, to_expr ``(and.right %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.iff p) := do
  t ← mk_mvar, to_expr ``(iff.mpr %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.eq p) := do
  t ← mk_mvar, to_expr ``(cast (eq.symm %%t)) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_intro and_kind.and p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(and.intro %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.and_intro and_kind.iff p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(iff.intro %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.and_intro and_kind.eq p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(propext (iff.intro %%t₁ %%t₂)) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.curry ak p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (proof.curry₂ ak p (proof.hyp n))
| Γ (proof.curry₂ ak p q) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (q.and_intro ak (proof.hyp n)))
| Γ (proof.app' p q) := do
  A ← mk_meta_var (expr.sort level.zero),
  B ← mk_meta_var (expr.sort level.zero),
  g₁ ← mk_meta_var `((%%A : Prop) → (%%B : Prop)),
  g₂ ← mk_meta_var A,
  g :: gs ← get_goals,
  unify (g₁ g₂) g,
  set_goals (g₁::g₂::gs) >> apply_proof Γ p >> apply_proof Γ q
| Γ (proof.or_imp_left p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (proof.hyp n).or_inl)
| Γ (proof.or_imp_right p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (proof.hyp n).or_inr)
| Γ (proof.or_inl p) := do
  t ← mk_mvar, to_expr ``(or.inl %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.or_inr p) := do
  t ← mk_mvar, to_expr ``(or.inr %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.or_elim' p x p₁ p₂) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, t₃ ← mk_mvar, to_expr ``(or.elim %%t₁ %%t₂ %%t₃) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::t₃::gs), apply_proof Γ p,
  e ← intro_core x, apply_proof (Γ.insert x e) p₁,
  e ← intro_core x, apply_proof (Γ.insert x e) p₂
| Γ (proof.em ff n) := do
  e ← Γ.find n,
  to_expr ``(@decidable.em _ %%e) >>= exact
| Γ (proof.em tt n) := do
  e ← Γ.find n,
  to_expr ``(@classical.em %%e) >>= exact
| Γ (proof.decidable_elim ff n x p₁ p₂) := do
  e ← Γ.find n,
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(@dite _ _ %%e %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs),
  e ← intro_core x, apply_proof (Γ.insert x e) p₁,
  e ← intro_core x, apply_proof (Γ.insert x e) p₂
| Γ (proof.decidable_elim tt n x p₁ p₂) := do
  e ← Γ.find n,
  e ← to_expr ``(@classical.dec %%e),
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(@dite _ _ %%e %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs),
  e ← intro_core x, apply_proof (Γ.insert x e) p₁,
  e ← intro_core x, apply_proof (Γ.insert x e) p₂
| Γ (proof.imp_imp_simp x p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (proof.intro x (proof.hyp n)))

end itauto

open itauto

/-- A decision procedure for intuitionistic propositional logic.

* `use_dec` will add `a ∨ ¬ a` to the context for every decidable atomic proposition `a`.
* `use_classical` will allow `a ∨ ¬ a` to be added even if the proposition is not decidable,
  using classical logic.
* `extra_dec` will add `a ∨ ¬ a` to the context for specified (not necessarily atomic)
  propositions `a`.
-/
meta def itauto (use_dec use_classical : bool) (extra_dec : list expr) : tactic unit :=
using_new_ref mk_buffer $ λ atoms,
using_new_ref mk_name_map $ λ hs, do
  t ← target,
  t ← mcond (is_prop t) (reify atoms t) (tactic.exfalso $> prop.false),
  hyps ← local_context,
  (Γ, decs) ← hyps.mfoldl
    (λ (Γ : except (prop → proof) context × native.rb_map prop (bool × expr)) h, do
      e ← infer_type h,
      mcond (is_prop e)
        (do A ← reify atoms e,
          let n := h.local_uniq_name,
          read_ref hs >>= λ Γ, write_ref hs (Γ.insert n h),
          pure (Γ.1 >>= λ Γ', Γ'.add A (proof.hyp n), Γ.2))
        (match e with
        | `(decidable %%p) :=
          if use_dec then do
            A ← reify atoms p,
            let n := h.local_uniq_name,
            pure (Γ.1, Γ.2.insert A (ff, h))
          else pure Γ
        | _ := pure Γ
        end))
    (except.ok native.mk_rb_map, native.mk_rb_map),
  let add_dec (force : bool) (decs : native.rb_map prop (bool × expr)) (e : expr) := (do
    A ← reify atoms e,
    dec_e ← mk_app ``decidable [e],
    res ← try_core (mk_instance dec_e),
    if res.is_none ∧ ¬ use_classical then
      if force then do
        m ← mk_meta_var dec_e,
        set_goals [m] >> apply_instance >> failure
      else pure decs
    else
      pure (native.rb_map.insert decs A (res.elim (tt, e) (prod.mk ff)))),
  decs ← extra_dec.mfoldl (add_dec tt) decs,
  decs ← if use_dec then do
    let decided := match Γ with
    | except.ok Γ := Γ.fold native.mk_rb_set $ λ p _ m, match p with
      | prop.var i := m.insert i
      | prop.not (prop.var i) := m.insert i
      | _ := m
      end
    | except.error _ := native.mk_rb_set
    end,
    read_ref atoms >>= λ ats, ats.2.iterate (pure decs) $ λ i e r,
      if decided.contains i.1 then r else r >>= λ decs, add_dec ff decs e
  else pure decs,
  Γ ← decs.fold (pure Γ) (λ A ⟨cl, pf⟩ r, r >>= λ Γ, do
    n ← mk_fresh_name,
    read_ref hs >>= λ Γ, write_ref hs (Γ.insert n pf),
    pure (Γ >>= λ Γ', Γ'.add (A.or A.not) (proof.em cl n))),
  let p := match Γ with
  | except.ok Γ := (prove Γ t 0).2.1
  | except.error p := p t
  end,
  hs ← read_ref hs, apply_proof hs p

namespace interactive
setup_tactic_parser

/-- A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle (without the `!` option), and the proof search is
tailored for this use case. (`itauto!` will work as a classical SAT solver, but the algorithm is
not very good in this situation.)

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
`decidable a` and `decidable b`. `itauto *` will case on all decidable propositions that it can
find among the atomic propositions, and `itauto! *` will case on all propositional atoms.
*Warning:* This can blow up the proof search, so it should be used sparingly.
-/
meta def itauto (classical : parse (tk "!")?)
  : parse (some <$> pexpr_list <|> none <$ tk "*")? → tactic unit
| none := tactic.itauto false classical.is_some []
| (some none) := tactic.itauto true classical.is_some []
| (some (some ls)) := ls.mmap i_to_expr >>= tactic.itauto false classical.is_some

add_hint_tactic "itauto"

add_tactic_doc
{ name       := "itauto",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.itauto],
  tags       := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }

end interactive
end tactic
