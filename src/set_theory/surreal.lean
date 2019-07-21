/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The basic theory of surreal numbers.
-/
import set_theory.game

namespace pgame

/- Multiplicative operations can be defined at the level of pre-games, but as
they are only useful on surreal numbers, so we define them here. -/

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
  `{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
def mul (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
  { exact IHxl i y + IHyl j - IHxl i (yL j) },
  { exact IHxr i y + IHyr j - IHxr i (yR j) },
  { exact IHxl i y + IHyr j - IHxl i (yR j) },
  { exact IHxr i y + IHyl j - IHxr i (yL j) }
end

instance : has_mul pgame := ⟨mul⟩

/-- Because the two halves of the definition of inv produce more elements
  of each side, we have to define the two families inductively.
  This is the indexing set for the function, and `inv_val` is the function part. -/
inductive {u} inv_ty (l r : Type u) : bool → Type u
| zero {} : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

/-- Because the two halves of the definition of inv produce more elements
  of each side, we have to define the two families inductively.
  This is the function part, defined by recursion on `inv_ty`. -/
def inv_val {l r} (L : l → pgame) (R : r → pgame)
  (IHl : l → pgame) (IHr : r → pgame) : ∀ {b}, inv_ty l r b → pgame
| _ inv_ty.zero := 0
| _ (inv_ty.left₁ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i
| _ (inv_ty.left₂ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₁ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₂ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i

/-- The inverse of a positive surreal number `x = {L | R}` is
  given by `x⁻¹ = {0,
    (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
    (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
  Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
  definition, the sets and elements are inductively generated. -/
def inv' : pgame → pgame
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pgame := λ i, L i.1,
      IHl' : l' → pgame := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

/-- The inverse of a surreal number in terms of the inverse on
  positive surreals. -/
noncomputable def inv (x : pgame) : pgame :=
by classical; exact
if x = 0 then 0 else if 0 < x then inv' x else inv' (-x)

noncomputable instance : has_inv pgame := ⟨inv⟩
noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

/-- A pre-surreal is valid (wikipedia calls this "numeric") if
  everything in the L set is less than everything in the R set,
  and all the elements of L and R are also valid. -/
def numeric : pgame → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ (∀ i, numeric (R i))

@[elab_as_eliminator]
theorem numeric_rec {C : pgame → Prop}
  (H : ∀ l r (L : l → pgame) (R : r → pgame),
    (∀ i j, L i < R j) → (∀ i, numeric (L i)) → (∀ i, numeric (R i)) →
    (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
  ∀ x, numeric x → C x
| ⟨l, r, L, R⟩ ⟨h, hl, hr⟩ :=
  H _ _ _ _ h hl hr (λ i, numeric_rec _ (hl i)) (λ i, numeric_rec _ (hr i))

theorem numeric_zero : numeric 0 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨by rintros ⟨⟩, by rintros ⟨⟩⟩⟩
theorem numeric_one : numeric 1 :=
⟨by rintros ⟨⟩ ⟨⟩, ⟨λ x, numeric_zero, by rintros ⟨⟩⟩⟩

theorem numeric_neg : Π {x : pgame} (o : numeric x), numeric (-x)
| ⟨l, r, L, R⟩ o :=
⟨λ j i, lt_iff_neg_gt.1 (o.1 i j),
  ⟨λ j, numeric_neg (o.2.2 j), λ i, numeric_neg (o.2.1 i)⟩⟩

-- TODO prove numeric_add

theorem lt_asymm {x y : pgame} (ox : numeric x) (oy : numeric y) : x < y → ¬ y < x :=
begin
  refine numeric_rec (λ xl xr xL xR hx oxl oxr IHxl IHxr, _) x ox y oy,
  refine numeric_rec (λ yl yr yL yR hy oyl oyr IHyl IHyr, _),
  simp, rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩),
  { exact IHxl _ _ (oyl _) (lt_of_le_mk h₁) (lt_of_le_mk h₂) },
  { exact not_lt.2 (le_trans h₂ h₁) (hy _ _) },
  { exact not_lt.2 (le_trans h₁ h₂) (hx _ _) },
  { exact IHxr _ _ (oyr _) (lt_of_mk_le h₁) (lt_of_mk_le h₂) },
end

theorem le_of_lt {x y : pgame} (ox : numeric x) (oy : numeric y) (h : x < y) : x ≤ y :=
not_lt.1 (lt_asymm ox oy h)

theorem lt_iff_le_not_le {x y : pgame} (ox : numeric x) (oy : numeric y) : x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
⟨λ h, ⟨le_of_lt ox oy h, not_le.2 h⟩, λ h, not_le.1 h.2⟩

end pgame

/-- The equivalence on valid pre-surreal numbers. -/
def surreal.equiv (x y : {x // pgame.numeric x}) : Prop := x.1.equiv y.1
local infix ` ≈ ` := surreal.equiv

instance surreal.setoid : setoid {x // pgame.numeric x} :=
⟨λ x y, x.1.equiv y.1,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of surreal numbers. In ZFC, a surreal number is constructed from
  two sets of surreal numbers that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-surreal is built
  inductively from two families of pre-surreals indexed over any type
  in Type u. The resulting type `pSurreal.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A surreal number is then constructed by discarding the invalid pre-surreals
  and quotienting by equivalence so that the ordering becomes a total order. -/
def surreal := quotient surreal.setoid

namespace surreal
open pgame

/-- Construct a surreal number from a valid pre-surreal. -/
def mk (x : pgame) (h : x.numeric) : surreal := quotient.mk ⟨x, h⟩

instance : has_zero surreal :=
{ zero := ⟦⟨0, numeric_zero⟩⟧ }
instance : has_one surreal :=
{ one := ⟦⟨1, numeric_one⟩⟧ }

/-- Lift an equivalence-respecting function on pre-surreals to surreals. -/
def lift {α} (f : ∀ x, numeric x → α)
  (H : ∀ {x y} (hx : numeric x) (hy : numeric y), x.equiv y → f x hx = f y hy) : surreal → α :=
quotient.lift (λ x : {x // numeric x}, f x.1 x.2) (λ x y, H x.2 y.2)

/-- Lift a binary equivalence-respecting function on pre-surreals to surreals. -/
def lift₂ {α} (f : ∀ x y, numeric x → numeric y → α)
  (H : ∀ {x₁ y₁ x₂ y₂} (ox₁ : numeric x₁) (oy₁ : numeric y₁) (ox₂ : numeric x₂) (oy₂ : numeric y₂),
    x₁.equiv x₂ → y₁.equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) : surreal → surreal → α :=
lift (λ x ox, lift (λ y oy, f x y ox oy) (λ y₁ y₂ oy₁ oy₂ h, H _ _ _ _ (equiv_refl _) h))
  (λ x₁ x₂ ox₁ ox₂ h, funext $ quotient.ind $ by exact λ ⟨y, oy⟩, H _ _ _ _ h (equiv_refl _))

/-- The relation `x ≤ y` on surreals. -/
def le : surreal → surreal → Prop :=
lift₂ (λ x y _ _, x ≤ y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (le_congr hx hy))

/-- The relation `x < y` on surreals. -/
def lt : surreal → surreal → Prop :=
lift₂ (λ x y _ _, x < y) (λ x₁ y₁ x₂ y₂ _ _ _ _ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : surreal}, ¬ le x y ↔ lt y x :=
by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; exact not_le

instance : preorder surreal :=
{ le := le,
  lt := lt,
  le_refl := by rintro ⟨⟨x, ox⟩⟩; exact le_refl _,
  le_trans := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ ⟨⟨z, oz⟩⟩; exact le_trans,
  lt_iff_le_not_le := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; exact lt_iff_le_not_le ox oy }

instance : partial_order surreal :=
{ le_antisymm := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ h₁ h₂; exact quot.sound ⟨h₁, h₂⟩,
  ..surreal.preorder }

instance : linear_order surreal :=
{ le_total := by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; classical; exact
    or_iff_not_imp_left.2 (λ h, le_of_lt oy ox (pgame.not_le.1 h)),
  ..surreal.partial_order }

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO construct instances for add_semigroup, add_monoid, add_group, add_comm_semigroup,
-- add_comm_group, ordered_comm_group, as per the instances for `game`

-- TODO define the inclusion of groups `surreal → game`

-- TODO define the dyadic rationals, and show they map into the surreals via the formula
--   m / 2^n ↦ { (m-1) / 2^n | (m+1) / 2^n }
-- TODO show this is a group homomorphism, and injective

-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective

-- TODO define the field structure on the surreals
-- TODO show the maps from the dyadic rationals and from the reals into the surreals are multiplicative

end surreal
