/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.list.chain
/-!
# The coproduct of a family of groups

We work with an `ι`-indexed family `G` of monoids, where both `ι` and all `G i` have decidable
equality. We define the coproduct `coprod G` of `G` as the type of reduced words. One could define
this more abstractly in terms of its presentation, but this definition has the advantage of giving
decidable equality.

When `G i` are all groups, we show that `coprod G` is also a group.

## Main definitions

- `coprod G`
- `of {i}`: the embedding `G i →* coprod G`.
- `ump X : (Π {i}, G i →* X) ≃ (coprod G →* X)`: the universal mapping property of the coproduct.

-/

open list

section monoids

variables {ι : Type*} (G : Π i : ι, Type*) [Π i, monoid (G i)]
  [decidable_eq ι] [∀ i, decidable_eq (G i)]

@[derive decidable_eq]
def coprod : Type* := { l : list (Σ i, { g : G i // g ≠ 1 }) // (l.map sigma.fst).chain' (≠) }
variable {G}

-- `w.head_isn't i` says that `i` is not the head of `w`.
def coprod.head_isn't (w : coprod G) (i : ι) : Prop := ∀ p ∈ (w.val.map sigma.fst).head', i ≠ p

section cases
-- here we define a custom eliminator for `coprod`. The idea is we have an index `i`, and
-- want to say that every `w : coprod G` either (1) doesn't have `i` as its head, or (2) is `g * w'`
-- for some `g : G i`, where `w'` doesn't have `i` as its head.
variables {i : ι} {C : coprod G → Sort*}
  (d1 : Π w : coprod G, w.head_isn't i → C w)
  (d2 : Π (w : coprod G) (h : w.head_isn't i) (g), C ⟨⟨i, g⟩ :: w.val, w.property.cons' h⟩)
include d1 d2

def coprod_cases : Π w : coprod G, C w
| w@⟨[], _⟩ := d1 w $ by rintro _ ⟨⟩
| w@⟨⟨j, g⟩ :: ls, h⟩ := if ij : i = j then by { cases ij, exact d2 ⟨ls, h.tail⟩ h.rel_head' g }
else d1 w $ by { rintro _ ⟨⟩ ⟨⟩, exact ij rfl }

variables {d1 d2}

-- computation rule for the first case of our eliminator
lemma beta1 : ∀ (w : coprod G) h, (coprod_cases d1 d2 w : C w) = d1 w h
| ⟨[], _⟩ h := rfl
| ⟨⟨j, g⟩ :: ls, hl⟩ h := by { rw [coprod_cases, dif_neg], exact h j rfl }

-- computation rule for the second case of our eliminator
lemma beta2 (w : coprod G) (h : w.head_isn't i) (g) {x} :
  (coprod_cases d1 d2 ⟨⟨i, g⟩ :: w.val, x⟩ : C ⟨⟨i, g⟩ :: w.val, x⟩) = d2 w h g :=
by { rw [coprod_cases, dif_pos rfl], cases w, refl }

end cases

-- prepend `g : G i` to `w`, assuming `i` is not the head of `w`.
def rcons' {i : ι} (g : G i) (w : coprod G) (h : w.head_isn't i) : coprod G :=
if g_one : g = 1 then w else ⟨⟨i, g, g_one⟩ :: w.val, w.property.cons' h⟩

-- prepend `g : G i` to `w`. NB this is defined in terms of `rcons'`: this will be a recurring theme.
def rcons {i : ι} (g : G i) : coprod G → coprod G :=
coprod_cases (rcons' g) (λ w h g', rcons' (g * ↑g') w h)

-- computation rules for `rcons`
lemma rcons_def1 {i : ι} {g : G i} {w : coprod G} (h) : rcons g w = rcons' g w h := beta1 _ _
lemma rcons_def2 {i : ι} {g : G i} {w : coprod G} (h) (g') {x} :
  rcons g ⟨⟨i, g'⟩ :: w.val, x⟩ = rcons' (g * ↑g') w h := beta2 _ _ _

-- prepending one doesn't change our word
lemma rcons_one {i : ι} : ∀ w : coprod G, rcons (1 : G i) w = w :=
begin
  apply coprod_cases,
  { intros w h, rw [rcons_def1 h, rcons', dif_pos rfl], },
  { rintros w h ⟨g, hg⟩, rw [rcons_def2 h, one_mul, rcons', dif_neg], refl, }
end

-- preliminary for `rcons_mul`
private lemma rcons_mul' {i : ι} {g g' : G i} (w : coprod G) (h : w.head_isn't i) :
  rcons (g * g') w = rcons g (rcons g' w) :=
begin
  rw [rcons_def1 h, rcons_def1 h, rcons', rcons'],
  split_ifs,
  { rw [h_2, mul_one] at h_1, rw [h_1, rcons_one], },
  { rw [rcons_def2 h, rcons', dif_pos], exact h_1, },
  { rw [rcons_def1 h, rcons', dif_neg], { congr, rw [h_2, mul_one], }, simpa [h_2] using h_1, },
  { rw [rcons_def2 h, rcons', dif_neg], refl, },
end

-- we can prepend `g * g'` one element at a time.
lemma rcons_mul {i : ι} (g : G i) (g' : G i) : ∀ w, rcons (g * g') w = rcons g (rcons g' w) :=
coprod_cases rcons_mul' $ λ w h g'',
by rw [rcons_def2 h, rcons_def2 h, mul_assoc, ←rcons_def1, rcons_mul' _ h, ←rcons_def1]

-- Every `G i` thus acts on the coproduct.
@[simps] instance bar (i) : mul_action (G i) (coprod G) :=
{ smul := rcons, one_smul := rcons_one, mul_smul := rcons_mul }

-- Prepending a letter to a word means acting on that word. This will be useful for proofs by
-- induction on words.
lemma cons_as_smul {i} {g} (ls) (hl) :
 (⟨⟨i, g⟩ :: ls, hl⟩ : coprod G) = (g.val • ⟨ls, hl.tail⟩ : coprod G) :=
begin
  rw [bar_to_has_scalar_smul, rcons_def1, rcons', dif_neg g.property],
  { congr, ext, refl, }, { exact hl.rel_head', },
end

section action
-- Given actions of `G i` on `X`, the coproduct also has a scalar action on `X`. We'll use this
-- both to define multiplication in the coproduct, and to get its universal property.
variables {X : Type*} [∀ i, mul_action (G i) X]

instance foo : has_scalar (coprod G) X := ⟨λ g x, g.val.foldr (λ l y, l.snd.val • y) x⟩

-- preliminary for `foobar`.
private lemma foobar' {i} {g : G i} {x : X} (w : coprod G) (h : w.head_isn't i) :
  (rcons g w) • x = g • (w • x) :=
by { rw [rcons_def1 h, rcons'], split_ifs, { rw [h_1, one_smul], }, { refl, }, }

-- (I'm not sure it's worth it to use these typeclasses, since Lean gets a bit confused by them...)
instance foobar (i) : is_scalar_tower (G i) (coprod G) X :=
⟨begin
  intros g' w x,
  refine coprod_cases foobar' _ w,
  intros,
  rw [rcons_def2 h, ←rcons_def1 h, foobar' _ h, mul_smul],
  refl,
end⟩

end action

instance coprod_monoid : monoid (coprod G) :=
{ mul := λ x y, x • y,
  mul_assoc := begin
    rintros ⟨ls, hl⟩ b c,
    change (_ • _) • _ = _ • (_ • _),
    induction ls with p ls ih,
    { refl, },
    cases p with i g,
    rw [cons_as_smul, smul_assoc g.val _ b, smul_assoc, ih, smul_assoc],
    apply_instance, -- ??
  end,
  one := ⟨[], chain'_nil⟩,
  one_mul := λ _, rfl,
  mul_one := begin
    rintro ⟨ls, hl⟩,
    change _ • _ = _,
    induction ls with p ls ih,
    { refl },
    { cases p with i g, rw [cons_as_smul, smul_assoc, ih], },
  end }

def of {i} : G i →* coprod G :=
{ to_fun := λ g, g • 1,
  map_one' := rcons_one _,
  map_mul' := by { intros, change rcons _ _ = _ • _, rw [rcons_mul, smul_assoc], refl } }

lemma cons_as_mul {i} {g} (ls) (h) :
 (⟨⟨i, g⟩ :: ls, h⟩ : coprod G) = (of g.val * ⟨ls, h.tail⟩ : coprod G) :=
by { convert cons_as_smul ls h, change (_ • _) • _ = _, rw smul_assoc g.val, congr, apply_instance }

def ump (X : Type*) [monoid X] :
  (Π {i}, G i →* X) ≃ (coprod G →* X) :=
{ to_fun := λ fi, begin
    letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ fi,
    refine { to_fun := λ g, g • 1, map_one' := rfl, map_mul' := _ },
    rintros ⟨ls, hl⟩ b,
    change (_ • _) • _ = _,
    induction ls with p ls ih,
    { exact (one_mul _).symm },
    cases p with i g,
    rw [cons_as_smul, smul_assoc g.val _ b, smul_assoc, ih, smul_assoc],
    { exact (mul_assoc _ _ _).symm },
    { apply_instance },
  end,
  inv_fun := λ f i, f.comp of,
  left_inv := begin
    intro fi, letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ fi,
    ext i g, change (g • (1 : coprod G)) • (1 : X) = fi g,
    rw smul_assoc, apply mul_one,
  end,
  right_inv := begin
    intro f,
    ext w,
    cases w with ls hl,
    change _ • 1 = f ⟨ls, hl⟩,
    induction ls with p ls ih,
    { exact f.map_one.symm },
    cases p with i g,
    conv_rhs { rw [cons_as_mul, f.map_mul] },
    letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ (f.comp of),
    rw [cons_as_smul, smul_assoc, ih], refl
  end }

lemma prod_eq_self (w : coprod G) : list.prod (w.val.map (λ l, of l.snd.val)) = w :=
begin
  cases w with ls hl, induction ls with p ls ih,
  { refl, }, { cases p, rw [map_cons, prod_cons, ih hl.tail, cons_as_mul], },
end

end monoids

-- we now do the case of groups.
variables {ι : Type*} {G : Π i : ι, Type*} [Π i, group (G i)]
  [decidable_eq ι] [∀ i, decidable_eq (G i)]

@[simps] instance coprod_inv : has_inv (coprod G) :=
⟨λ w, ⟨reverse (w.val.map $ λ l, ⟨l.fst, l.snd.val⁻¹, inv_ne_one.mpr l.snd.property⟩),
  by simpa [eq_comm, flip, chain'_reverse] using w.property⟩⟩

instance : group (coprod G) :=
{ mul_left_inv := begin
    intro w, -- possibly this should all be deduced from some more general result
    conv_lhs { congr, rw ←prod_eq_self w⁻¹, skip, rw ←prod_eq_self w },
    cases w with ls junk,
    rw [subtype.val_eq_coe, coprod_inv_inv_coe, map_reverse, map_map],
    dsimp only, clear junk,
    induction ls with p ls ih,
    { apply mul_one, },
    rw [map_cons, reverse_cons, prod_append, map_cons, prod_cons, prod_nil, mul_one,
      function.comp_apply, mul_assoc, prod_cons, ←mul_assoc _ (of p.snd.val), ←of.map_mul,
      mul_left_inv, of.map_one, one_mul, ih],
  end,
  ..coprod_inv,
  ..coprod_monoid }
