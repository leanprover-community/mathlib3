/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The basic theory of surreal numbers.
-/
import tactic.interactive data.nat.cast

/-- The type of pre-surreal numbers, before we have quotiented
  by extensionality. In ZFC, a surreal number is constructed from
  two sets of surreal numbers that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-surreal is built
  inductively from two families of pre-surreals indexed over any type
  in Type u. The resulting type `pSurreal.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive {u} pSurreal : Type (u+1)
| mk : ∀ α β : Type u, (α → pSurreal) → (β → pSurreal) → pSurreal

namespace pSurreal

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on surreals. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  So we define `x < y` and `x <= y` simultaneously. -/
def le_lt (x y : pSurreal) : Prop × Prop :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  exact (
    (∀ i, (IHxl i ⟨yl, yr, yL, yR⟩).2) ∧ (∀ i, (IHyr i).2),
    (∃ i, (IHxr i ⟨yl, yr, yL, yR⟩).1) ∨ (∃ i, (IHyl i).1))
end

instance : has_le pSurreal := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pSurreal := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-surreals. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pSurreal) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ i, (⟨xl, xr, xL, xR⟩ : pSurreal) < yR i) := iff.rfl

/-- Definition of `x < y` on pre-surreals. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pSurreal) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ i, xR i ≤ ⟨yl, yr, yL, yR⟩) ∨
  (∃ i, (⟨xl, xr, xL, xR⟩ : pSurreal) ≤ yL i) := iff.rfl

theorem lt_of_le_mk {xl xr xL xR y i} :
  (⟨xl, xr, xL, xR⟩ : pSurreal) ≤ y → xL i < y :=
by cases y; exact λ h, h.1 i

theorem lt_of_mk_le {x : pSurreal} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by cases x; exact λ h, h.2 i

theorem mk_lt_of_le {xl xr xL xR y i} :
  (by exact xR i ≤ y) → (⟨xl, xr, xL, xR⟩ : pSurreal) < y :=
by cases y; exact λ h, or.inl ⟨i, h⟩

theorem lt_mk_of_le {x : pSurreal} {yl yr yL yR i} :
  (by exact x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by cases x; exact λ h, or.inr ⟨i, h⟩

theorem not_le_lt {x y : pSurreal} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp [not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr]
end

theorem not_le {x y : pSurreal} : ¬ x ≤ y ↔ y < x := not_le_lt.1
theorem not_lt {x y : pSurreal} : ¬ x < y ↔ y ≤ x := not_le_lt.2

theorem le_refl : ∀ x : pSurreal, x ≤ x
| ⟨l, r, L, R⟩ :=
  ⟨λ i, lt_mk_of_le (le_refl _), λ i, mk_lt_of_le (le_refl _)⟩

theorem lt_irrefl (x : pSurreal) : ¬ x < x :=
not_lt.2 (le_refl _)

theorem ne_of_lt : ∀ {x y : pSurreal}, x < y → x ≠ y
| x _ h rfl := lt_irrefl x h

/-- A pre-surreal is valid (wikipedia calls this "numeric") if
  everything in the L set is less than everything in the R set,
  and all the elements of L and R are also valid. -/
def ok : pSurreal → Prop
| ⟨l, r, L, R⟩ :=
  (∀ i j, L i < R j) ∧ (∀ i, ok (L i)) ∧ (∀ i, ok (R i))

@[elab_as_eliminator]
theorem ok_rec {C : pSurreal → Prop}
  (H : ∀ l r (L : l → pSurreal) (R : r → pSurreal),
    (∀ i j, L i < R j) → (∀ i, ok (L i)) → (∀ i, ok (R i)) →
    (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
  ∀ x, ok x → C x
| ⟨l, r, L, R⟩ ⟨h, hl, hr⟩ :=
  H _ _ _ _ h hl hr (λ i, ok_rec _ (hl i)) (λ i, ok_rec _ (hr i))

theorem le_trans_aux
  {xl xr} {xL : xl → pSurreal} {xR : xr → pSurreal}
  {yl yr} {yL : yl → pSurreal} {yR : yr → pSurreal}
  {zl zr} {zL : zl → pSurreal} {zR : zr → pSurreal}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
  λ i, not_le.1 (λ h, not_lt.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _)),
  λ i, not_le.1 (λ h, not_lt.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _))⟩

theorem le_trans {x y z : pSurreal} : x ≤ y → y ≤ z → x ≤ z :=
suffices ∀ {x y z : pSurreal},
  (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
from this.1, begin
  clear x y z, intros,
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  induction z with zl zr zL zR IHzl IHzr,
  exact ⟨
    le_trans_aux (λ i, (IHxl _).2.1) (λ i, (IHzr _).2.2),
    le_trans_aux (λ i, (IHyl _).2.2) (λ i, (IHxr _).1),
    le_trans_aux (λ i, (IHzl _).1) (λ i, (IHyr _).2.1)⟩,
end

theorem lt_asymm {x y : pSurreal}
  (ox : ok x) (oy : ok y) : x < y → ¬ y < x :=
begin
  refine ok_rec (λ xl xr xL xR hx oxl oxr IHxl IHxr, _) x ox y oy,
  refine ok_rec (λ yl yr yL yR hy oyl oyr IHyl IHyr, _),
  simp, rintro (⟨i, h₁⟩ | ⟨i, h₁⟩) (⟨j, h₂⟩ | ⟨j, h₂⟩),
  { exact IHxr _ _ (oyr _) (lt_of_mk_le h₁) (lt_of_mk_le h₂) },
  { exact not_lt.2 (le_trans h₁ h₂) (hx _ _) },
  { exact not_lt.2 (le_trans h₂ h₁) (hy _ _) },
  { exact IHxl _ _ (oyl _) (lt_of_le_mk h₁) (lt_of_le_mk h₂) }
end

theorem le_of_lt {x y : pSurreal} (ox : ok x) (oy : ok y) (h : x < y) : x ≤ y :=
not_lt.1 (lt_asymm ox oy h)

theorem lt_iff_le_not_le {x y : pSurreal}
  (ox : ok x) (oy : ok y) : x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
⟨λ h, ⟨le_of_lt ox oy h, not_le.2 h⟩, λ h, not_le.1 h.2⟩

/-- Define the equivalence relation on pre-surreals. Two pre-surreals
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pSurreal) : Prop := x ≤ y ∧ y ≤ x

theorem equiv_refl (x) : equiv x x := ⟨le_refl _, le_refl _⟩
theorem equiv_symm {x y} : equiv x y → equiv y x | ⟨xy, yx⟩ := ⟨yx, xy⟩
theorem equiv_trans {x y z} : equiv x y → equiv y z → equiv x z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

theorem le_congr {x₁ y₁ x₂ y₂} : equiv x₁ x₂ → equiv y₁ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ :=
  ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : equiv x₁ x₂) (hy : equiv y₁ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

/-- The pre-surreal zero is defined by `0 = { | }`. -/
instance : has_zero pSurreal := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

/-- The pre-surreal one is defined by `1 = { 0 | }`. -/
instance : has_one pSurreal := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pSurreal → pSurreal
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pSurreal := ⟨neg⟩

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is
  `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : pSurreal) : pSurreal :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact λ i, IHyl i },
  { exact λ i, IHxr i y },
  { exact λ i, IHyr i }
end

instance : has_add pSurreal := ⟨add⟩

instance : has_sub pSurreal := ⟨λ x y, x + -y⟩

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
  `{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR |
    xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
def mul (x y : pSurreal) : pSurreal :=
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

instance : has_mul pSurreal := ⟨mul⟩

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
def inv_val {l r} (L : l → pSurreal) (R : r → pSurreal)
  (IHl : l → pSurreal) (IHr : r → pSurreal) : ∀ {b}, inv_ty l r b → pSurreal
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
def inv' : pSurreal → pSurreal
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pSurreal := λ i, L i.1,
      IHl' : l' → pSurreal := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

/-- The inverse of a surreal number in terms of the inverse on
  positive surreals. -/
noncomputable def inv (x : pSurreal) : pSurreal :=
by classical; exact
if x = 0 then 0 else if 0 < x then inv' x else inv' (-x)

noncomputable instance : has_inv pSurreal := ⟨inv⟩
noncomputable instance : has_div pSurreal := ⟨λ x y, x * y⁻¹⟩

/-- The pre-surreal number `ω`. (In fact all ordinals have surreal
  representatives.) -/
def omega : pSurreal := ⟨ulift ℕ, pempty, λ n, ↑n.1, pempty.elim⟩

end pSurreal

/-- The equivalence on valid pre-surreal numbers. -/
def surreal.equiv (x y : {x // pSurreal.ok x}) : Prop := x.1.equiv y.1
local infix ` ≈ ` := surreal.equiv

instance surreal.setoid : setoid {x // pSurreal.ok x} :=
⟨λ x y, x.1.equiv y.1,
 λ x, pSurreal.equiv_refl _,
 λ x y, pSurreal.equiv_symm,
 λ x y z, pSurreal.equiv_trans⟩

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
open pSurreal

/-- Construct a surreal number from a valid pre-surreal. -/
def mk (x : pSurreal) (h : x.ok) : surreal := quotient.mk ⟨x, h⟩

/-- Lift an equivalence-respecting function on pre-surreals to surreals. -/
def lift {α} (f : ∀ x, ok x → α) (H : ∀ {x y} (hx : ok x) (hy : ok y), x.equiv y → f x hx = f y hy) : surreal → α :=
quotient.lift (λ x : {x // ok x}, f x.1 x.2) (λ x y, H x.2 y.2)

/-- Lift a binary equivalence-respecting function on pre-surreals to surreals. -/
def lift₂ {α} (f : ∀ x y, ok x → ok y → α)
  (H : ∀ {x₁ y₁ x₂ y₂} (ox₁ : ok x₁) (oy₁ : ok y₁) (ox₂ : ok x₂) (oy₂ : ok y₂),
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
    or_iff_not_imp_left.2 (λ h, le_of_lt oy ox (pSurreal.not_le.1 h)),
  ..surreal.partial_order }

end surreal
