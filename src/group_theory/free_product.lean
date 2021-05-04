/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.list.chain
/-!
# The free product of groups or monoids

Given an `ι`-indexed family `M` of monoids, where both `ι` and all `M i` have decidable
equality, we define the free product `free_product M` of `M` as the type of reduced words, and show
that it has the universal property of a coproduct. One could define the free product more abstractly
in terms of its presentation, but this definition has the advantage of giving decidable equality.

When `M i` are all groups, we show that `free_product M` is also a group.

## Main definitions

- `free_product M`
- `of {i}`: the embedding `M i →* free_product M`.
- `lift X : (Π {i}, M i →* X) ≃ (free_product M →* X)`: the free product is a categorical coproduct.

## Idea

We define the monoid structure on `free_product M` by letting each `M i` act on `free_product M`.
One way to understand this is that each `M i` thus maps into the monoid
`free_product M → free_product M`, and the submonoid generated by their images bijects with
`free_product M` by evaluation at `[]`, inducing a monoid structure on `free_product M`.
We take the shortcut of not introducing `free_product M → free_product M` or this bijection.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

variables {ι : Type*} (M : Π i : ι, Type*) [Π i, monoid (M i)]
  [decidable_eq ι] [∀ i, decidable_eq (M i)]

/-- `free_product M` is the free product, or categorical coproduct, of a family `M` of monoids.
This assumes that the indexing type and each monoid all have decidable equality. -/
@[derive decidable_eq, nolint unused_arguments]
def free_product : Type* := { l : list (Σ i, { m : M i // m ≠ 1 }) // (l.map sigma.fst).chain' (≠) }
variable {M}

namespace free_product

instance : has_one (free_product M) := ⟨⟨[], list.chain'_nil⟩⟩
instance : inhabited (free_product M) := ⟨1⟩

/-- Prepend `m : M i` to `w` assuming `i` is not the first index in `w`. If `m = 1`, do nothing. -/
def rcons {i} (m : M i) (w : free_product M) (h : ∀ p ∈ (w.val.map sigma.fst).head', i ≠ p) :
  free_product M := if m_one : m = 1 then w else ⟨⟨i, m, m_one⟩ :: w.val, w.property.cons' h⟩

lemma rcons_one {i} (w : free_product M) (h) : rcons (1 : M i) w h = w := dif_pos rfl
lemma rcons_ne_one {i} {m : M i} (hm : m ≠ 1) {w : free_product M} (h) :
  rcons m w h = ⟨⟨i, m, hm⟩ :: w.val, w.property.cons' h⟩ := dif_neg hm
lemma cons_eq_rcons {i m ls hl} :
  (⟨⟨i, m⟩ :: ls, hl⟩ : free_product M) = rcons m.val ⟨ls, hl.tail⟩ hl.rel_head' :=
by { cases m with m hm, rw rcons_ne_one hm, refl, }

/-- A custom eliminator for the free product. The idea is that any reduced word can be uniquely
expressed as `rcons m w h` with `m : M i`, where `m = 1` if `i` is not the word's first index. -/
def cases {i : ι} (C : free_product M → Sort*)
  (d : Π (m : M i) (w : free_product M) (h), C (rcons m w h)) :
  Π w : free_product M, C w
| w@⟨[], _⟩ := @eq.rec _ _ C (d 1 w $ by rintro _ ⟨⟩) _ (rcons_one w _)
| w@⟨⟨j, m⟩ :: ls, h⟩ := if ij : i = j then by { cases ij, rw cons_eq_rcons, apply d, }
else @eq.rec _ _ C (d 1 w $ by { rintro _ ⟨⟩, exact ij }) _ (rcons_one w _)

/-- Computation rule for `free_product.cases` in the non-dependent case. -/
lemma cases_def {i : ι} {C : Sort*} {d} (m : M i) (w : free_product M) (h) :
  (rcons m w h).cases (λ _, C) d = d m w h :=
begin
  by_cases hm : m = 1,
  { rw [hm, rcons_one],
    rcases w with ⟨⟨⟩ | ⟨⟨j, m'⟩, ls⟩, hl ⟩,
    { rw [free_product.cases, eq_rec_constant]},
    { rw [free_product.cases, dif_neg (h j rfl), eq_rec_constant], }, },
  { rw [rcons_ne_one hm, free_product.cases, dif_pos rfl], cases w, refl, },
end

instance (i) : mul_action (M i) (free_product M) :=
{ smul := λ m w, w.cases _ $ λ m' w' h, rcons (m * m') w' h,
  one_smul := λ w, w.cases _ $ λ m' w' h, by { dsimp only, rw [cases_def, one_mul] },
  mul_smul := λ m m' w, w.cases _ $ λ m'' w' h,
    by { dsimp only, rw [cases_def, cases_def, cases_def, mul_assoc] } }

lemma smul_rcons (i) (m m' : M i) (w h) : m • rcons m' w h = rcons (m * m') w h :=
cases_def m' w h

lemma cons_eq_smul {i m ls hl} :
  (⟨⟨i, m⟩ :: ls, hl⟩ : free_product M) = (m.val • ⟨ls, hl.tail⟩ : free_product M) :=
by rw [←rcons_one ⟨ls, hl.tail⟩ hl.rel_head', smul_rcons, mul_one, cons_eq_rcons]

@[elab_as_eliminator]
lemma smul_induction {C : free_product M → Prop} (w : free_product M)
  (h_one : C 1) (h_smul : ∀ i (m : M i) w, C w → C (m • w)) : C w :=
begin
  cases w with ls hl,
  induction ls with p ls ih,
  { exact h_one },
  cases p with i m,
  rw cons_eq_smul,
  exact h_smul i m.val _ (ih _),
end

section action
variables {X Y : Type*} [∀ i, mul_action (M i) X] [∀ i, mul_action (M i) Y]
  [has_scalar X Y] [∀ i, is_scalar_tower (M i) X Y]

/-- Given actions of `M i` on `X`, the free product also acts on `X`. We use this
both to define multiplication in the free product and to get its universal property. -/
instance : has_scalar (free_product M) X := ⟨λ w x, w.val.foldr (λ p y, p.snd.val • y) x⟩

instance (i) : is_scalar_tower (M i) (free_product M) X :=
⟨λ m' w x, w.cases _ $ λ m'' w' h, have key : ∀ m : M i, rcons m w' h • x = m • (w' • x),
  from λ m, if hm : m = 1 then by rw [hm, rcons_one, one_smul]
            else by { rw rcons_ne_one hm, refl },
  by rw [smul_rcons, key, key, mul_smul]⟩

instance tower_of_tower : is_scalar_tower (free_product M) X Y :=
{ smul_assoc := λ a x y, smul_induction a rfl $ λ i m a' ih,
  by rw [smul_assoc m a' x, smul_assoc m (a' • x) y, smul_assoc m a' (x • y), ih] }

instance : monoid (free_product M) :=
{ mul := λ x y, x • y,
  mul_assoc := smul_assoc,
  one_mul := λ a, rfl,
  mul_one := λ a, smul_induction a rfl $ λ i m b ih, by { dsimp only at *, rw [smul_assoc, ih] },
  ..free_product.has_one }

instance action_of_free_product : mul_action (free_product M) X :=
{ one_smul := λ x, rfl, mul_smul := λ a b x, smul_assoc a b x }

end action

instance {G : ι → Type*} [Π i, group (G i)] [Π i, decidable_eq (G i)] : group (free_product G) :=
{ inv := λ w, ⟨list.reverse (w.val.map $ λ l, ⟨l.fst, l.snd.val⁻¹, inv_ne_one.mpr l.snd.property⟩),
    by simpa [eq_comm, flip, list.chain'_reverse] using w.property⟩,
  mul_left_inv := λ ⟨ls, hl⟩, begin
    change list.foldr _ _ (list.reverse _) = _,
    induction ls with p ls ih,
    { refl },
    cases p with i m,
    rw [list.map_cons, list.reverse_cons, list.foldr_append, list.foldr, list.foldr,
      cons_eq_smul, smul_smul, mul_left_inv, one_smul, ih]
  end,
  ..free_product.monoid }

lemma mul_eq_smul (a b : free_product M) : a * b = a • b := rfl

/-- The inclusion into the free product. -/
@[simps] def of {i} : M i →* free_product M :=
{ to_fun := λ m, m • 1,
  map_one' := one_smul _ _,
  map_mul' := by { intros, rw [mul_smul, mul_eq_smul, smul_one_smul], } }

lemma smul_eq_of_mul {i} {m : M i} {w : free_product M} : m • w = of m * w :=
by rw [of_apply, mul_eq_smul, smul_one_smul]

/-- The universal property of the free product: a monoid homomorphism from the `free_product M` is
uniquely determined by a family of homomorphisms from the `M i`.-/
def lift {X : Type*} [monoid X] : (Π {i}, M i →* X) ≃ (free_product M →* X) :=
{ to_fun := λ fi, begin
    letI : ∀ i, mul_action (M i) X := λ i, mul_action.comp_hom _ fi,
    refine { to_fun := λ w, w • 1, map_one' := rfl, map_mul' := λ a b, _ },
    haveI : ∀ i, is_scalar_tower (M i) X X := λ i, ⟨λ a b c, mul_assoc (fi a) b c⟩,
    have : ∀ (x y : X), (a • x) * y = a • (x * y) := smul_assoc a,
    rw [mul_smul, this, one_mul],
  end,
  inv_fun := λ f i, f.comp of,
  left_inv := λ fi, begin
    ext i m,
    change (m • _) • (1 : X) = fi m,
    letI : mul_action (M i) X := mul_action.comp_hom _ fi,
    rw smul_assoc,
    exact mul_one (fi m),
  end,
  right_inv := λ f, begin
    ext w,
    change w • _ = _,
    refine smul_induction w f.map_one.symm _,
    intros i m w' ih,
    letI : mul_action (M i) X := mul_action.comp_hom _ (f.comp of),
    rw [smul_assoc, smul_eq_of_mul, f.map_mul, ih],
    refl,
  end }

lemma prod_eq_self : ∀ w : free_product M, list.prod (w.val.map (λ l, of l.snd.val)) = w
| ⟨ls, hl⟩ := begin
  induction ls with p ls ih,
  { refl, },
  { cases p, rw [list.map_cons, list.prod_cons, ih hl.tail, cons_eq_smul, smul_eq_of_mul], },
end

end free_product
