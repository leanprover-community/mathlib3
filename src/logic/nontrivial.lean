/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import logic.unique
import logic.function.basic

/-!
# Nontrivial types

A type is *nontrivial* if it contains at least two elements. This is useful in particular for rings
(where it is equivalent to the fact that zero is different from one) and for vector spaces
(where it is equivalent to the fact that the dimension is positive).

We introduce a typeclass `nontrivial` formalizing this property.
-/

variables {α : Type*} {β : Type*}

open_locale classical

/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class nontrivial (α : Type*) : Prop :=
(exists_pair_ne : ∃ (x y : α), x ≠ y)

lemma nontrivial_iff : nontrivial α ↔ ∃ (x y : α), x ≠ y :=
⟨λ h, h.exists_pair_ne, λ h, ⟨h⟩⟩

lemma exists_pair_ne (α : Type*) [nontrivial α] : ∃ (x y : α), x ≠ y :=
nontrivial.exists_pair_ne

lemma exists_ne [nontrivial α] (x : α) : ∃ y, y ≠ x :=
begin
  rcases exists_pair_ne α with ⟨y, y', h⟩,
  by_cases hx : x = y,
  { rw ← hx at h,
    exact ⟨y', h.symm⟩ },
  { exact ⟨y, ne.symm hx⟩ }
end

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
lemma nontrivial_of_ne (x y : α) (h : x ≠ y) : nontrivial α :=
⟨⟨x, y, h⟩⟩

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
lemma nontrivial_of_lt [preorder α] (x y : α) (h : x < y) : nontrivial α :=
⟨⟨x, y, ne_of_lt h⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance nontrivial.to_nonempty [nontrivial α] : nonempty α :=
let ⟨x, _⟩ := exists_pair_ne α in ⟨x⟩

/-- An inhabited type is either nontrivial, or has a unique element. -/
noncomputable def nontrivial_psum_unique (α : Type*) [inhabited α] :
  psum (nontrivial α) (unique α) :=
if h : nontrivial α then psum.inl h else psum.inr
{ default := default α,
  uniq := λ (x : α),
  begin
    change x = default α,
    contrapose! h,
    use [x, default α]
  end }

lemma subsingleton_iff : subsingleton α ↔ ∀ (x y : α), x = y :=
⟨by { introsI h, exact subsingleton.elim }, λ h, ⟨h⟩⟩

lemma not_nontrivial_iff_subsingleton : ¬(nontrivial α) ↔ subsingleton α :=
by { rw [nontrivial_iff, subsingleton_iff], push_neg, refl }

lemma not_subsingleton (α) [h : nontrivial α] : ¬subsingleton α :=
let ⟨⟨x, y, hxy⟩⟩ := h in λ ⟨h'⟩, hxy $ h' x y

/-- A type is either a subsingleton or nontrivial. -/
lemma subsingleton_or_nontrivial (α : Type*) : subsingleton α ∨ nontrivial α :=
by { rw [← not_nontrivial_iff_subsingleton, or_comm], exact classical.em _ }

lemma false_of_nontrivial_of_subsingleton (α : Type*) [nontrivial α] [subsingleton α] : false :=
let ⟨x, y, h⟩ := exists_pair_ne α in h $ subsingleton.elim x y

instance nontrivial_prod_left [nontrivial α] [nonempty β] : nontrivial (α × β) :=
begin
  inhabit β,
  rcases exists_pair_ne α with ⟨x, y, h⟩,
  use [(x, default β), (y, default β)],
  contrapose! h,
  exact congr_arg prod.fst h
end

instance nontrivial_prod_right [nontrivial α] [nonempty β] : nontrivial (β × α) :=
begin
  inhabit β,
  rcases exists_pair_ne α with ⟨x, y, h⟩,
  use [(default β, x), (default β, y)],
  contrapose! h,
  exact congr_arg prod.snd h
end

instance option.nontrivial [nonempty α] : nontrivial (option α) :=
by { inhabit α, use [none, some (default α)] }

instance function.nontrivial [nonempty α] [nontrivial β] : nontrivial (α → β) :=
begin
  rcases exists_pair_ne β with ⟨x, y, h⟩,
  use [λ _, x, λ _, y],
  contrapose! h,
  inhabit α,
  exact congr_fun h (default α)
end

/-- Pushforward a `nontrivial` instance along an injective function. -/
protected lemma function.injective.nontrivial [nontrivial α]
  {f : α → β} (hf : function.injective f) : nontrivial β :=
let ⟨x, y, h⟩ := exists_pair_ne α in ⟨⟨f x, f y, hf.ne h⟩⟩

/-- Pullback a `nontrivial` instance along a surjective function. -/
protected lemma function.surjective.nontrivial [nontrivial β]
  {f : α → β} (hf : function.surjective f) : nontrivial α :=
begin
  rcases exists_pair_ne β with ⟨x, y, h⟩,
  rcases hf x with ⟨x', hx'⟩,
  rcases hf y with ⟨y', hy'⟩,
  have : x' ≠ y', by { contrapose! h, rw [← hx', ← hy', h] },
  exact ⟨⟨x', y', this⟩⟩
end

/-- An injective function from a nontrivial type has an argument at
which it does not take a given value. -/
protected lemma function.injective.exists_ne [nontrivial α] {f : α → β}
  (hf : function.injective f) (y : β) : ∃ x, f x ≠ y :=
begin
  rcases exists_pair_ne α with ⟨x₁, x₂, hx⟩,
  by_cases h : f x₂ = y,
  { exact ⟨x₁, (hf.ne_iff' h).2 hx⟩ },
  { exact ⟨x₂, h⟩ }
end

mk_simp_attribute nontriviality "Simp lemmas for `nontriviality` tactic"

protected lemma subsingleton.le [preorder α] [subsingleton α] (x y : α) : x ≤ y :=
le_of_eq (subsingleton.elim x y)

attribute [nontriviality] eq_iff_true_of_subsingleton subsingleton.le

namespace tactic

/--
Tries to generate a `nontrivial α` instance by performing case analysis on
`subsingleton_or_nontrivial α`,
attempting to discharge the subsingleton branch using lemmas with `@[nontriviality]` attribute,
including `subsingleton.le` and `eq_iff_true_of_subsingleton`.
-/
meta def nontriviality_by_elim (α : expr) (lems : interactive.parse simp_arg_list) : tactic unit :=
do
  alternative ← to_expr ``(subsingleton_or_nontrivial %%α),
  n ← get_unused_name "_inst",
  tactic.cases alternative [n, n],
  (solve1 $ do
    reset_instance_cache,
    interactive.simp none ff lems [`nontriviality] (interactive.loc.ns [none])) <|>
      fail format!"Could not prove goal assuming `subsingleton {α}`",
  reset_instance_cache

/--
Tries to generate a `nontrivial α` instance using `nontrivial_of_ne` or `nontrivial_of_lt`
and local hypotheses.
-/
meta def nontriviality_by_assumption (α : expr) : tactic unit :=
do
  n ← get_unused_name "_inst",
  to_expr ``(nontrivial %%α) >>= assert n,
  apply_instance <|> `[solve_by_elim [nontrivial_of_ne, nontrivial_of_lt]],
  reset_instance_cache

end tactic

namespace tactic.interactive

open tactic

setup_tactic_parser

/--
Attempts to generate a `nontrivial α` hypothesis.

The tactic first looks for an instance using `apply_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `nontrivial` instance directly.

Otherwise, it will perform a case split on `subsingleton α ∨ nontrivial α`, and attempt to discharge
the `subsingleton` goal using `simp [lemmas] with nontriviality`, where `[lemmas]` is a list of
additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using [lemmas]`.

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  assumption,
end
```

```
example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality, -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm,
end
```

```
example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 :=
begin
  nontriviality R, -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
end
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b :=
begin
  success_if_fail { nontriviality α }, -- Fails
  nontriviality α using [myeq], -- There is now a `nontrivial α` hypothesis available
  assumption
end
```
-/
meta def nontriviality (t : parse texpr?)
  (lems : parse (tk "using" *> simp_arg_list <|> pure [])) :
  tactic unit :=
do
  α ← match t with
  | some α := to_expr α
  | none :=
    (do t ← mk_mvar, e ← to_expr ``(@eq %%t _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@has_le.le %%t _ _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@ne %%t _ _), target >>= unify e, return t) <|>
    (do t ← mk_mvar, e ← to_expr ``(@has_lt.lt %%t _ _ _), target >>= unify e, return t) <|>
    fail "The goal is not an (in)equality, so you'll need to specify the desired `nontrivial α`
      instance by invoking `nontriviality α`."
  end,
  nontriviality_by_assumption α <|> nontriviality_by_elim α lems

add_tactic_doc
{ name                     := "nontriviality",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.nontriviality],
  tags                     := ["logic", "typeclass"] }

end tactic.interactive
