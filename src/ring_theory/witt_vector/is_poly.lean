/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import algebra.ring.ulift
import ring_theory.witt_vector.basic
import data.mv_polynomial.funext

/-!
# The `is_poly` predicate

`witt_vector.is_poly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → mv_polynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `is_poly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `witt_vector.frobenius`
and `witt_vector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `witt_vector.is_poly`, `witt_vector.is_poly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `witt_vector.is_poly.ext`, `witt_vector.is_poly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `witt_vector.is_poly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `witt_vector.id_is_poly`, `witt_vector.neg_is_poly`,
  `witt_vector.add_is_poly₂`, `witt_vector.mul_is_poly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attributes `@[is_poly]` and `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

Any atomic proof of `is_poly` or `is_poly₂` (i.e. not taking additional `is_poly` arguments)
should be tagged as `@[is_poly]`.

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
begin
  ghost_calc _,
  <minor preprocessing>,
  ghost_simp
end
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

/-
### Simplification tactics

`ghost_simp` is used later in the development for certain simplifications.
We define it here so it is a shared import.
-/

mk_simp_attribute ghost_simps
"Simplification rules for ghost equations"

namespace tactic
namespace interactive
setup_tactic_parser

/-- A macro for a common simplification when rewriting with ghost component equations. -/
meta def ghost_simp (lems : parse simp_arg_list) : tactic unit :=
do tactic.try tactic.intro1,
   simp none none tt
     (lems ++ [simp_arg_type.symm_expr ``(sub_eq_add_neg)])
     [`ghost_simps] (loc.ns [none])

/--
`ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
meta def ghost_calc (ids' : parse ident_*) : tactic unit :=
do ids ← ids'.mmap $ λ n, get_local n <|> tactic.intro n,
   `(@eq (witt_vector _ %%R) _ _) ← target,
   match ids with
   | [x] := refine ```(is_poly.ext _ _ _ _ %%x)
   | [x, y] := refine ```(is_poly₂.ext _ _ _ _ %%x %%y)
   | _ := fail "ghost_calc takes one or two arguments"
   end,
   nm ← match R with
   | expr.local_const _ nm _ _ := return nm
   | _ := get_unused_name `R
   end,
   iterate_exactly 2 apply_instance,
   unfreezingI (tactic.clear' tt [R]),
   introsI $ [nm, nm<.>"_inst"] ++ ids',
   skip

end interactive

end tactic

namespace witt_vector
universe variable u

variables {p : ℕ} {R S : Type u} {σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

open mv_polynomial
open function (uncurry)

include hp
variables (p)

noncomputable theory

/-!
### The `is_poly` predicate
-/

lemma poly_eq_of_witt_polynomial_bind_eq' (f g : ℕ → mv_polynomial (idx × ℕ) ℤ)
  (h : ∀ n, bind₁ f (witt_polynomial p _ n) = bind₁ g (witt_polynomial p _ n)) :
  f = g :=
begin
  ext1 n,
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  rw ← function.funext_iff at h,
  replace h := congr_arg
    (λ fam, bind₁ (mv_polynomial.map (int.cast_ring_hom ℚ) ∘ fam)
    (X_in_terms_of_W p ℚ n)) h,
  simpa only [function.comp, map_bind₁, map_witt_polynomial,
    ← bind₁_bind₁, bind₁_witt_polynomial_X_in_terms_of_W, bind₁_X_right] using h
end

lemma poly_eq_of_witt_polynomial_bind_eq (f g : ℕ → mv_polynomial ℕ ℤ)
  (h : ∀ n, bind₁ f (witt_polynomial p _ n) = bind₁ g (witt_polynomial p _ n)) :
  f = g :=
begin
  ext1 n,
  apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
  rw ← function.funext_iff at h,
  replace h := congr_arg
    (λ fam, bind₁ (mv_polynomial.map (int.cast_ring_hom ℚ) ∘ fam)
    (X_in_terms_of_W p ℚ n)) h,
  simpa only [function.comp, map_bind₁, map_witt_polynomial,
    ← bind₁_bind₁, bind₁_witt_polynomial_X_in_terms_of_W, bind₁_X_right] using h
end

omit hp

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib

/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `witt_vector.is_poly₂` for the binary variant.

The `ghost_calc` tactic treats `is_poly` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly f`.
For the most part, users are not expected to treat `is_poly` as a class.
-/
class is_poly (f : Π ⦃R⦄ [comm_ring R], witt_vector p R → 𝕎 R) : Prop :=
mk' :: (poly : ∃ φ : ℕ → mv_polynomial ℕ ℤ, ∀ ⦃R⦄ [comm_ring R] (x : 𝕎 R),
  by exactI (f x).coeff = λ n, aeval x.coeff (φ n))

/-- The identity function on Witt vectors is a polynomial function. -/
instance id_is_poly : is_poly p (λ _ _, id) :=
⟨⟨X, by { introsI, simp only [aeval_X, id] }⟩⟩

instance id_is_poly_i' : is_poly p (λ _ _ a, a) :=
witt_vector.id_is_poly _

namespace is_poly

instance : inhabited (is_poly p (λ _ _, id)) :=
⟨witt_vector.id_is_poly p⟩

variables {p}
include hp
lemma ext {f g} (hf : is_poly p f) (hg : is_poly p g)
  (h : ∀ (R : Type u) [_Rcr : comm_ring R] (x : 𝕎 R) (n : ℕ),
    by exactI ghost_component n (f x) = ghost_component n (g x)) :
  ∀ (R : Type u) [_Rcr : comm_ring R] (x : 𝕎 R), by exactI f x = g x :=
begin
  unfreezingI
  { obtain ⟨φ, hf⟩ := hf,
    obtain ⟨ψ, hg⟩ := hg },
  intros,
  ext n,
  rw [hf, hg, poly_eq_of_witt_polynomial_bind_eq p φ ψ],
  intro k,
  apply mv_polynomial.funext,
  intro x,
  simp only [hom_bind₁],
  specialize h (ulift ℤ) (mk p $ λ i, ⟨x i⟩) k,
  simp only [ghost_component_apply, aeval_eq_eval₂_hom] at h,
  apply (ulift.ring_equiv.symm : ℤ ≃+* _).injective,
  simp only [←ring_equiv.coe_to_ring_hom, map_eval₂_hom],
  convert h using 1,
  all_goals {
    funext i,
    simp only [hf, hg, mv_polynomial.eval, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    simp only [coeff_mk], refl }
end

omit hp

/-- The composition of polynomial functions is polynomial. -/
lemma comp {g f} (hg : is_poly p g) (hf : is_poly p f) :
  is_poly p (λ R _Rcr, @g R _Rcr ∘ @f R _Rcr) :=
begin
  unfreezingI
  { obtain ⟨φ, hf⟩ := hf,
    obtain ⟨ψ, hg⟩ := hg },
  use (λ n, bind₁ φ (ψ n)),
  intros,
  simp only [aeval_bind₁, function.comp, hg, hf]
end

end is_poly

/--
A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `witt_vector.is_poly` for the unary variant.

The `ghost_calc` tactic treats `is_poly₂` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly₂ f`.
For the most part, users are not expected to treat `is_poly₂` as a class.
-/
class is_poly₂ (f : Π ⦃R⦄ [comm_ring R], witt_vector p R → 𝕎 R → 𝕎 R) : Prop :=
mk' :: (poly : ∃ φ : ℕ → mv_polynomial (fin 2 × ℕ) ℤ, ∀ ⦃R⦄ [comm_ring R] (x y : 𝕎 R),
  by exactI (f x y).coeff = λ n, peval (φ n) ![x.coeff, y.coeff])


variable {p}

/-- The composition of polynomial functions is polynomial. -/
lemma is_poly₂.comp {h f g} (hh : is_poly₂ p h) (hf : is_poly p f) (hg : is_poly p g) :
  is_poly₂ p (λ R _Rcr x y, by exactI h (f x) (g y)) :=
begin
  unfreezingI
  { obtain ⟨φ, hf⟩ := hf,
    obtain ⟨ψ, hg⟩ := hg,
    obtain ⟨χ, hh⟩ := hh },
  refine ⟨⟨(λ n, bind₁ (uncurry $
          ![λ k, rename (prod.mk (0 : fin 2)) (φ k),
            λ k, rename (prod.mk (1 : fin 2)) (ψ k)]) (χ n)), _⟩⟩,
  intros,
  funext n,
  simp only [peval, aeval_bind₁, function.comp, hh, hf, hg, uncurry],
  apply eval₂_hom_congr rfl _ rfl,
  ext ⟨i, n⟩,
  fin_cases i;
  simp only [aeval_eq_eval₂_hom, eval₂_hom_rename, function.comp, matrix.cons_val_zero,
    matrix.head_cons, matrix.cons_val_one],
end

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
lemma is_poly.comp₂ {g f} (hg : is_poly p g) (hf : is_poly₂ p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x y)) :=
begin
  unfreezingI
  { obtain ⟨φ, hf⟩ := hf,
    obtain ⟨ψ, hg⟩ := hg },
  use (λ n, bind₁ φ (ψ n)),
  intros,
  simp only [peval, aeval_bind₁, function.comp, hg, hf]
end

/-- The diagonal `λ x, f x x` of a polynomial function `f` is polynomial. -/
lemma is_poly₂.diag {f} (hf : is_poly₂ p f) :
  is_poly p (λ R _Rcr x, by exactI f x x) :=
begin
  unfreezingI {obtain ⟨φ, hf⟩ := hf},
  refine ⟨⟨λ n, bind₁ (uncurry ![X, X]) (φ n), _⟩⟩,
  intros, funext n,
  simp only [hf, peval, uncurry, aeval_bind₁],
  apply eval₂_hom_congr rfl _ rfl,
  ext ⟨i, k⟩, fin_cases i;
  simp only [matrix.head_cons, aeval_X, matrix.cons_val_zero, matrix.cons_val_one],
end

namespace tactic
open tactic

/-!
### The `@[is_poly]` attribute

This attribute is used to derive specialized composition instances
for `is_poly` and `is_poly₂` declarations.
-/

/--
If `n` is the name of a lemma with opened type `∀ vars, is_poly p _`,
`mk_poly_comp_lemmas n vars p` adds composition instances to the environment
`n.comp_i` and `n.comp₂_i`.
-/
meta def mk_poly_comp_lemmas (n : name) (vars : list expr) (p : expr) : tactic unit :=
do c ← mk_const n,
   let appd := vars.foldl expr.app c,

   tgt_bod ← to_expr ``(λ f [hf : is_poly %%p f], is_poly.comp %%appd hf) >>=
     replace_univ_metas_with_univ_params,
   tgt_bod ← lambdas vars tgt_bod,
   tgt_tp ← infer_type tgt_bod,
   let nm := n <.> "comp_i",
   add_decl $ mk_definition nm tgt_tp.collect_univ_params tgt_tp tgt_bod,
   set_attribute `instance nm,

   tgt_bod ← to_expr ``(λ f [hf : is_poly₂ %%p f], is_poly.comp₂ %%appd hf) >>=
     replace_univ_metas_with_univ_params,
   tgt_bod ← lambdas vars tgt_bod,
   tgt_tp ← infer_type tgt_bod,
   let nm := n <.> "comp₂_i",
   add_decl $ mk_definition nm tgt_tp.collect_univ_params tgt_tp tgt_bod,
   set_attribute `instance nm

/--
If `n` is the name of a lemma with opened type `∀ vars, is_poly₂ p _`,
`mk_poly₂_comp_lemmas n vars p` adds composition instances to the environment
`n.comp₂_i` and `n.comp_diag`.
-/
meta def mk_poly₂_comp_lemmas (n : name) (vars : list expr) (p : expr) : tactic unit :=
do c ← mk_const n,
   let appd := vars.foldl expr.app c,

   tgt_bod ← to_expr ``(λ {f g} [hf : is_poly %%p f] [hg : is_poly %%p g],
     is_poly₂.comp %%appd hf hg) >>= replace_univ_metas_with_univ_params,
   tgt_bod ← lambdas vars tgt_bod,
   tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify,
   let nm := n <.> "comp₂_i",
   add_decl $ mk_definition nm tgt_tp.collect_univ_params tgt_tp tgt_bod,
   set_attribute `instance nm,

   tgt_bod ← to_expr ``(λ {f g} [hf : is_poly %%p f] [hg : is_poly %%p g],
     (is_poly₂.comp %%appd hf hg).diag) >>= replace_univ_metas_with_univ_params,
   tgt_bod ← lambdas vars tgt_bod,
   tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify,
   let nm := n <.> "comp_diag",
   add_decl $ mk_definition nm tgt_tp.collect_univ_params tgt_tp tgt_bod,
   set_attribute `instance nm

/--
The `after_set` function for `@[is_poly]`. Calls `mk_poly(₂)_comp_lemmas`.
-/
meta def mk_comp_lemmas (n : name) : tactic unit :=
do d ← get_decl n,
   (vars, tp) ← open_pis d.type,
   match tp with
   | `(is_poly %%p _) := mk_poly_comp_lemmas n vars p
   | `(is_poly₂ %%p _) := mk_poly₂_comp_lemmas n vars p
   | _ := fail "@[is_poly] should only be applied to terms of type `is_poly _ _` or `is_poly₂ _ _`"
   end

/--
`@[is_poly]` is applied to lemmas of the form `is_poly f φ` or `is_poly₂ f φ`.
These lemmas should *not* be tagged as instances, and only atomic `is_poly` defs should be tagged:
composition lemmas should not. Roughly speaking, lemmas that take `is_poly` proofs as arguments
should not be tagged.

Type class inference struggles with function composition, and the higher order unification problems
involved in inferring `is_poly` proofs are complex. The standard style writing these proofs by hand
doesn't work very well. Instead, we construct the type class hierarchy "under the hood", with
limited forms of composition.

Applying `@[is_poly]` to a lemma creates a number of instances. Roughly, if the tagged lemma is a
proof of `is_poly f φ`, the instances added have the form
```lean
∀ g ψ, [is_poly g ψ] → is_poly (f ∘ g) _
```
Since `f` is fixed in this instance, it restricts the HO unification needed when the instance is
applied. Composition lemmas relating `is_poly` with `is_poly₂` are also added.
`id_is_poly` is an atomic instance.

The user-written lemmas are not instances. Users should be able to assemble `is_poly` proofs by hand
"as normal" if the tactic fails.
-/
@[user_attribute] meta def is_poly_attr : user_attribute :=
{ name := `is_poly,
  descr := "Lemmas with this attribute describe the polynomial structure of functions",
  after_set := some $ λ n _ _, mk_comp_lemmas n }

end tactic

include hp

/-!
### `is_poly` instances

These are not declared as instances at the top level,
but the `@[is_poly]` attribute adds instances based on each one.
Users are expected to use the non-instance versions manually.
-/

/-- The additive negation is a polynomial function on Witt vectors. -/
@[is_poly]
lemma neg_is_poly : is_poly p (λ R _, by exactI @has_neg.neg (𝕎 R) _) :=
⟨⟨λ n, rename prod.snd (witt_neg p n),
begin
  introsI, funext n,
  rw [neg_coeff, aeval_eq_eval₂_hom, eval₂_hom_rename],
  apply eval₂_hom_congr rfl _ rfl,
  ext ⟨i, k⟩, fin_cases i, refl,
end⟩⟩

section zero_one
/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/

/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
instance zero_is_poly : is_poly p (λ _ _ _, by exactI 0) :=
⟨⟨0, by { introsI, funext n, simp only [pi.zero_apply, alg_hom.map_zero, zero_coeff] }⟩⟩

@[simp] lemma bind₁_zero_witt_polynomial (n : ℕ) :
  bind₁ (0 : ℕ → mv_polynomial ℕ R) (witt_polynomial p R n) = 0 :=
by rw [← aeval_eq_bind₁, aeval_zero, constant_coeff_witt_polynomial, ring_hom.map_zero]

omit hp

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def one_poly (n : ℕ) : mv_polynomial ℕ ℤ := if n = 0 then 1 else 0

include hp

@[simp] lemma bind₁_one_poly_witt_polynomial (n : ℕ) :
  bind₁ one_poly (witt_polynomial p ℤ n) = 1 :=
begin
  rw [witt_polynomial_eq_sum_C_mul_X_pow, alg_hom.map_sum, finset.sum_eq_single 0],
  { simp only [one_poly, one_pow, one_mul, alg_hom.map_pow, C_1, pow_zero, bind₁_X_right,
      if_true, eq_self_iff_true], },
  { intros i hi hi0,
    simp only [one_poly, if_neg hi0, zero_pow (pow_pos hp.1.pos _), mul_zero,
      alg_hom.map_pow, bind₁_X_right, alg_hom.map_mul], },
  { rw finset.mem_range, dec_trivial }
end

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
instance one_is_poly : is_poly p (λ _ _ _, by exactI 1) :=
⟨⟨one_poly,
begin
  introsI, funext n, cases n,
  { simp only [one_poly, if_true, eq_self_iff_true, one_coeff_zero, alg_hom.map_one], },
  { simp only [one_poly, nat.succ_pos', one_coeff_eq_of_pos,
      if_neg n.succ_ne_zero, alg_hom.map_zero] }
end⟩⟩

end zero_one

omit hp

/-- Addition of Witt vectors is a polynomial function. -/
@[is_poly] lemma add_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (+)) :=
⟨⟨witt_add p, by { introsI, dunfold witt_vector.has_add, simp [eval] }⟩⟩


/-- Multiplication of Witt vectors is a polynomial function. -/
@[is_poly] lemma mul_is_poly₂ [fact p.prime] : is_poly₂ p (λ _ _, by exactI (*)) :=
⟨⟨witt_mul p, by { introsI, dunfold witt_vector.has_mul, simp [eval] }⟩⟩

include hp

-- unfortunately this is not universe polymorphic, merely because `f` isn't
lemma is_poly.map {f} (hf : is_poly p f) (g : R →+* S) (x : 𝕎 R) :
  map g (f x) = f (map g x) :=
begin
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `is_poly₂.map` for a slightly more general proof strategy
  unfreezingI {obtain ⟨φ, hf⟩ := hf},
  ext n,
  simp only [map_coeff, hf, map_aeval],
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  simp only [map_coeff]
end

namespace is_poly₂
omit hp
instance [fact p.prime] : inhabited (is_poly₂ p _) := ⟨add_is_poly₂⟩

variables {p}

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
lemma comp_left {g f} (hg : is_poly₂ p g) (hf : is_poly p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g (f x) y) :=
hg.comp hf (witt_vector.id_is_poly _)

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
lemma comp_right {g f} (hg : is_poly₂ p g) (hf : is_poly p f) :
  is_poly₂ p (λ R _Rcr x y, by exactI g x (f y)) :=
hg.comp (witt_vector.id_is_poly p) hf

include hp

lemma ext {f g} (hf : is_poly₂ p f) (hg : is_poly₂ p g)
  (h : ∀ (R : Type u) [_Rcr : comm_ring R] (x y : 𝕎 R) (n : ℕ),
    by exactI ghost_component n (f x y) = ghost_component n (g x y)) :
  ∀ (R) [_Rcr : comm_ring R] (x y : 𝕎 R), by exactI f x y = g x y :=
begin
  unfreezingI
  { obtain ⟨φ, hf⟩ := hf,
    obtain ⟨ψ, hg⟩ := hg },
  intros,
  ext n,
  rw [hf, hg, poly_eq_of_witt_polynomial_bind_eq' p φ ψ],
  clear x y,
  intro k,
  apply mv_polynomial.funext,
  intro x,
  simp only [hom_bind₁],
  specialize h (ulift ℤ) (mk p $ λ i, ⟨x (0, i)⟩) (mk p $ λ i, ⟨x (1, i)⟩) k,
  simp only [ghost_component_apply, aeval_eq_eval₂_hom] at h,
  apply (ulift.ring_equiv.symm : ℤ ≃+* _).injective,
  simp only [←ring_equiv.coe_to_ring_hom, map_eval₂_hom],
  convert h using 1,
  all_goals {
    funext i,
    simp only [hf, hg, mv_polynomial.eval, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext ⟨b, _⟩,
    fin_cases b; simp only [coeff_mk, uncurry]; refl }
end

-- unfortunately this is not universe polymorphic, merely because `f` isn't
lemma map {f} (hf : is_poly₂ p f) (g : R →+* S) (x y : 𝕎 R) :
  map g (f x y) = f (map g x) (map g y) :=
begin
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  unfreezingI {obtain ⟨φ, hf⟩ := hf},
  ext n,
  simp only [map_coeff, hf, map_aeval, peval, uncurry],
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  try { ext ⟨i, k⟩, fin_cases i },
  all_goals {
    simp only [map_coeff, matrix.cons_val_zero, matrix.head_cons, matrix.cons_val_one] },
end

end is_poly₂

attribute [ghost_simps]
      alg_hom.map_zero alg_hom.map_one alg_hom.map_add alg_hom.map_mul
      alg_hom.map_sub alg_hom.map_neg alg_hom.id_apply alg_hom.map_nat_cast
      ring_hom.map_zero ring_hom.map_one ring_hom.map_mul ring_hom.map_add
      ring_hom.map_sub ring_hom.map_neg ring_hom.id_apply ring_hom.map_nat_cast
      mul_add add_mul add_zero zero_add mul_one one_mul mul_zero zero_mul
      nat.succ_ne_zero nat.add_sub_cancel nat.succ_eq_add_one
      if_true eq_self_iff_true if_false forall_true_iff forall_2_true_iff forall_3_true_iff

end witt_vector
