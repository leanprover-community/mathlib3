import algebra.category.Group.abelian
open category_theory

namespace ITP

/-- The intuitive but problematic cochain complex definition. -/
structure cochain_complex :=
(X : ℤ → Ab) -- a family of abelian groups
(d : Π (n : ℤ), X n ⟶ X (n + 1)) -- a family of differentials
(d_comp_d : ∀ (n : ℤ), d n ≫ d (n + 1) = 0)
-- The notation `d n ≫ d (n + 1) = 0` means `dₙ₊₁ ∘ dₙ = 0.`


/- We can't try and prove `dₙ ∘ dₙ₋₁ = 0`, because the statement doesn't typecheck.
`X.d (n - 1)` has type `X.X (n - 1) ⟶ X.X (n - 1 + 1)`, and `X.X (n - 1 + 1)` is not
definitionally equal to `X.X n.` -/
/-lemma d_comp_d' (X : cochain_complex) (n : ℤ) :
  X.d (n - 1) ≫ X.d n = 0 := sorry-/

/-- Potential annoying solution: define an isomorphism `X.X (n - 1 + 1) ≅ X.X n`, then
compose this with the differential. -/
def eq_to_iso (X : cochain_complex) (n : ℤ) :
  X.X (n - 1 + 1) ≅ X.X n :=
eq.rec (iso.refl _) (int.sub_add_cancel n 1).symm

lemma d_comp_d (X : cochain_complex) (n : ℤ) :
  X.d (n - 1) ≫ (eq_to_iso X n).hom ≫ X.d n = 0 :=
begin
  convert X.d_comp_d (n - 1), -- We try and use the condition that `dₙ₋₁₊₁ ∘ dₙ₋₁ = 0`
  -- Leaving us with 5 goals! Some of them are just `n - 1 + 1 = n`:
  any_goals { rw int.sub_add_cancel n 1 }, -- So we `rewrite` the appropriate fact.
  -- But the last goal is perplexing: `==` means `heq`, or heterogeneous equality
  -- This is equality between types which aren't necessarily definitionally equal.
  /- If we try and `rewrite` the fact `n - 1 + 1 = n` in the type
  of `X.d (n - 1 + 1)`, we get an error 'motive is not type correct'; this is the problem with
  `rewriting` a type. -/
  -- rw int.sub_add_cancel n 1,
  sorry -- It is unclear what we can do! Working with `heq` can be difficult and unintuitive.
end

/- However, here is one possibility: Lean uses inductive types, and equality is an inductive type
  with one constructor:

inductive eq {α : Sort*} (a : α) : α → Prop
| refl [] : eq a

Therefore `eq` has an elimination principle: the `cases` tactic can eliminate a term of type
`H : i = j` in the local context of a lemma, replacing all occurrences of `i` with `j` in the
goal - even in types. Informally, we are case-splitting on the possible inductive constructors of
an inequality - but there is only one, the case when '`i` is `j`'.

From the description of the `cases` tactic:
"Assuming x is a variable in the local context with an inductive type, cases x splits the main goal,
producing one goal for each constructor of the inductive type, in which the target is replaced by a
general instance of that constructor. If the type of an element in the local context depends on x,
that element is reverted and reintroduced afterward, so that the case split affects that hypothesis
as well."

Thus we see we cannot use `cases` in the previous lemma: the target is replace by a 'general'
instance of a constructor, and in our setting, our equality term `n - 1 + 1 = n` was not general:
the righthand side depends on the lefthand side. If elimination principles replaced hypotheses like
this with more general statements, they would often be false, so attempting to use `cases`
must give an error.

But in our case, we can generalize: -/
def eq_to_iso_2 (X : cochain_complex) {i j : ℤ} (H : i = j) :
  X.X i ≅ X.X j :=
eq.rec (iso.refl _) H

/- We try and prove that `Xᵢ → Xⱼ → Xⱼ₊₁ = Xᵢ → Xᵢ₊₁ → Xⱼ₊₁`. -/
lemma d_comp_d_2 (X : cochain_complex) (i j : ℤ) (H : i = j) :
  (eq_to_iso_2 X H).hom ≫ X.d j = X.d i ≫ (eq_to_iso_2 X (by rw H)).hom :=
begin
/- Now, since both arguments to `eq` in the hypothesis `H` are local, independent
variables, we can use the `cases` tactic: -/
  cases H,
/- Our definition `eq_to_iso_2` used `eq.rec`, the recursion principle automatically generated
by `eq` being an inductive type. Ultimately this means that since we've used `cases`, `eq_to_iso2`
is now definitionally the identity, and both sides of the goal are definitionally equal: -/
  refl,
end

/- This principle is why the more general definition of a complex is a good idea. -/
structure improved_cochain_complex :=
(X : ℤ → Ab)
(d : Π (i j : ℤ), X i ⟶ X j)
(shape' : ∀ i j, ¬ (i + 1 = j) → d i j = 0)
(d_comp_d' : ∀ i j k, i + 1 = j → j + 1 = k → d i j ≫ d j k = 0)

end ITP
