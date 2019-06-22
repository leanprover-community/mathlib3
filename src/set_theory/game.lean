/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

The basic theory of combinatorial games. The surreal numbers will be built as a subtype.
-/
import tactic.interactive data.nat.cast data.equiv.basic

universes u

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame

namespace pgame

def left_moves : pgame → Type u
| (mk l _ _ _) := l
def right_moves : pgame → Type u
| (mk _ r _ _) := r

def move_left : Π (g : pgame), left_moves g → pgame
| (mk l _ L _) i := L i
def move_right : Π (g : pgame), right_moves g → pgame
| (mk _ r _ R) j := R j

@[simp] lemma left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).left_moves = xl := rfl
@[simp] lemma move_left_mk {xl xr xL xR i} : (⟨xl, xr, xL, xR⟩ : pgame).move_left i = xL i := rfl
@[simp] lemma right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).right_moves = xr := rfl
@[simp] lemma move_right_mk {xl xr xL xR j} : (⟨xl, xr, xL, xR⟩ : pgame).move_right j = xR j := rfl

inductive r : pgame → pgame → Prop
| left : Π (x : pgame) (i : x.left_moves), r (x.move_left i) x
| right : Π (x : pgame) (j : x.right_moves), r (x.move_right j) x
| trans : Π (x y z : pgame), r x y → r y z → r x z

def r.left' {xl xr} {xL : xl → pgame} {xR : xr → pgame} {i : xl} : r (xL i) (mk xl xr xL xR) :=
r.left (mk xl xr xL xR) (by { convert i, refl })
def r.right' {xl xr} {xL : xl → pgame} {xR : xr → pgame} {j : xr} : r (xR j) (mk xl xr xL xR) :=
r.right (mk xl xr xL xR) (by { convert j, refl })

theorem wf_r : well_founded r :=
⟨λ x, begin
  induction x with l r L R IHl IHr,
  refine ⟨_, λ y h, _⟩,
  generalize_hyp e : mk l r L R = x at h,
  induction h with _ i _ j a b _ h1 h2 IH1 IH2; subst e,
  { apply IHl },
  { apply IHr },
  { exact acc.inv (IH2 rfl) h1 }
end⟩

instance : has_well_founded pgame :=
{ r := r,
  wf := wf_r }

/-- The pre-surreal zero is defined by `0 = { | }`. -/
instance : has_zero pgame := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

@[simp] lemma zero_left_moves : (0 : pgame).left_moves = pempty := rfl
@[simp] lemma zero_right_moves : (0 : pgame).right_moves = pempty := rfl

/-- The pre-surreal one is defined by `1 = { 0 | }`. -/
instance : has_one pgame := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

@[simp] lemma one_left_moves : (1 : pgame).left_moves = punit := rfl
@[simp] lemma one_move_left : (1 : pgame).move_left punit.star = 0 := rfl
@[simp] lemma one_right_moves : (1 : pgame).right_moves = pempty := rfl

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  So we define `x < y` and `x <= y` simultaneously. -/
def le_lt (x y : pgame) : Prop × Prop :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  exact ((∀ i, (IHxl i ⟨yl, yr, yL, yR⟩).2) ∧ (∀ i, (IHyr i).2),
         (∃ i, (IHxr i ⟨yl, yr, yL, yR⟩).1) ∨ (∃ i, (IHyl i).1))
end

instance : has_le pgame := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pgame := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ i, (⟨xl, xr, xL, xR⟩ : pgame) < yR i) := iff.rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves, x.move_left i < y) ∧
  (∀ j : y.right_moves, x < y.move_right j) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩) ∨
  (∃ i, (⟨xl, xr, xL, xR⟩ : pgame) ≤ yL i) := iff.rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : pgame} : x < y ↔
  (∃ j : x.right_moves, x.move_right j ≤ y) ∨
  (∃ i : y.left_moves, x ≤ y.move_left i) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves,
   (∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ y) ∨
   (∃ i' : y.left_moves, (x.move_left i) ≤ (y.move_left i'))) ∧
  (∀ j : y.right_moves,
   (∃ j' : x.right_moves, x.move_right j' ≤ (y.move_right j)) ∨
   (∃ i : (y.move_right j).left_moves, x ≤ (y.move_right j).move_left i)) :=
begin
  rw [le_def_lt],
  conv { to_lhs, simp [lt_def_le] },
end

-- TODO corresponding lt_def

theorem forall_pempty {P : pempty → Prop} : (∀ x : pempty, P x) ↔ true :=
begin
  constructor,
  { intro h, trivial, },
  { rintros _ ⟨ ⟩, }
end
theorem exists_pempty {P : pempty → Prop} : (∃ x : pempty, P x) ↔ false :=
begin
  constructor,
  { rintro ⟨⟨ ⟩⟩ },
  { rintro ⟨ ⟩ },
end

theorem le_zero {x : pgame} : x ≤ 0 ↔
  ∀ i : x.left_moves, ∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ 0 :=
begin
  rw le_def,
  conv { to_lhs, congr, skip, erw [forall_pempty], },
  rw [and_true],
  constructor,
  { intros h i,
    have hi := h i,
    erw exists_pempty at hi,
    simpa using hi, },
  { intros h i,
    erw exists_pempty,
    rw [or_false],
    exact h i }
end

/-- Given a right-player-wins game, provide a response to any move by left. -/
noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) : (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) : (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

-- TODO define zero_le, left_response, and left_response_spec

theorem lt_of_le_mk {xl xr xL xR y i} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ y → xL i < y :=
by cases y; exact λ h, h.1 i

theorem lt_of_mk_le {x : pgame} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by cases x; exact λ h, h.2 i

theorem mk_lt_of_le {xl xr xL xR y i} :
  (by exact xR i ≤ y) → (⟨xl, xr, xL, xR⟩ : pgame) < y :=
by cases y; exact λ h, or.inl ⟨i, h⟩

theorem lt_mk_of_le {x : pgame} {yl yr yL yR i} :
  (by exact x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by cases x; exact λ h, or.inr ⟨i, h⟩

theorem not_le_lt {x y : pgame} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp [not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr]
end

theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := not_le_lt.1
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := not_le_lt.2

@[refl] theorem le_refl : ∀ x : pgame, x ≤ x
| ⟨l, r, L, R⟩ :=
  ⟨λ i, lt_mk_of_le (le_refl _), λ i, mk_lt_of_le (le_refl _)⟩

theorem lt_irrefl (x : pgame) : ¬ x < x :=
not_lt.2 (le_refl _)

theorem ne_of_lt : ∀ {x y : pgame}, x < y → x ≠ y
| x _ h rfl := lt_irrefl x h

theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
  λ i, not_le.1 (λ h, not_lt.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _)),
  λ i, not_le.1 (λ h, not_lt.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _))⟩

@[trans] theorem le_trans {x y z : pgame} : x ≤ y → y ≤ z → x ≤ z :=
suffices ∀ {x y z : pgame},
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

/-- Define the equivalence relation on pre-surreals. Two pre-surreals
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

theorem equiv_refl (x) : equiv x x := ⟨le_refl _, le_refl _⟩
theorem equiv_symm {x y} : equiv x y → equiv y x | ⟨xy, yx⟩ := ⟨yx, xy⟩
theorem equiv_trans {x y z} : equiv x y → equiv y z → equiv x z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

theorem le_congr {x₁ y₁ x₂ y₂} : equiv x₁ x₂ → equiv y₁ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ := ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : equiv x₁ x₂) (hy : equiv y₁ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) := rfl

theorem neg_neg : Π {x : pgame}, -(-x) = x
| (mk xl xr xL xR) :=
begin
  dsimp [has_neg.neg, neg],
  congr; funext i,
  { have t := @neg_neg (xL i),
    exact t },
  { have t := @neg_neg (xR i),
    exact t }
end

theorem neg_neg' {x : pgame} : neg (neg x) = x :=
begin
  have := neg_neg,
  dsimp [has_neg.neg] at this,
  exact this
end

theorem neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

def left_moves_neg {x : pgame} : (-x).left_moves ≃ x.right_moves :=
begin
  induction x,
  refl,
end
def right_moves_neg {x : pgame} : (-x).right_moves ≃ x.left_moves :=
begin
  induction x,
  refl,
end

-- FIXME, ugh, the current implementation of `solve_by_elim` apparently only uses each passed lemma
-- once. We cheat for now by repeating some of the lemmas!!
meta def pgame_wf_tac :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.left, psigma.lex.right, psigma.lex.right, r.left', r.right', r.left, r.right, r.trans]
  { max_rep := 10 }]

theorem le_iff_neg_ge : Π {x y : pgame}, x ≤ y ↔ -y ≤ -x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  rw [le_def],
  rw [le_def],
  dsimp [neg],
  fsplit,
  { intro h,
    fsplit,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.1 t_h, },
      { left,  cases t, use (@right_moves_neg (yR i)).symm t_w, convert le_iff_neg_ge.1 t_h, sorry } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use (@left_moves_neg (xL j)).symm t_w, convert le_iff_neg_ge.1 t_h, sorry },
      { left,  cases t, use t_w, exact le_iff_neg_ge.1 t_h, } } },
  { intro h,
    fsplit,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.2 t_h, },
      { left,  cases t, use (@left_moves_neg (xL i)) t_w, convert le_iff_neg_ge.2 _, convert t_h, sorry } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use (@right_moves_neg (yR j)) t_w, convert le_iff_neg_ge.2 _, convert t_h, sorry },
      { left,  cases t, use t_w, exact le_iff_neg_ge.2 t_h, } } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : pgame) : pgame :=
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

instance : has_add pgame := ⟨add⟩

def addL {xl xr yl yr} (xL : xl → pgame) (xR yL yR) (xy : xl ⊕ yl) : pgame :=
sum.cases_on xy (λ i, xL i + mk yl yr yL yR) (λ i, mk xl xr xL xR + yL i)

@[simp] lemma addL_inl {xl xr yl yr} (xL xR yL yR) (i : xl) :
  @addL xl xr yl yr xL xR yL yR (sum.inl i) = xL i + mk yl yr yL yR := rfl

@[simp] lemma addL_inr {xl xr yl yr} (xL xR yL yR) (i : yl) :
  @addL xl xr yl yr xL xR yL yR (sum.inr i) = mk xl xr xL xR + yL i := rfl

def addR {xl xr yl yr} (xL) (xR : xr → pgame) (yL yR) (xy : xr ⊕ yr) : pgame :=
sum.cases_on xy (λ i, xR i + mk yl yr yL yR) (λ i, mk xl xr xL xR + yR i)

@[simp] lemma addR_inl {xl xr yl yr} (xL xR yL yR) (i : xr) :
  @addR xl xr yl yr xL xR yL yR (sum.inl i) = xR i + mk yl yr yL yR := rfl

@[simp] lemma addR_inr {xl xr yl yr} (xL xR yL yR) (i : yr) :
  @addR xl xr yl yr xL xR yL yR (sum.inr i) = mk xl xr xL xR + yR i := rfl

lemma add_def {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
  mk xl xr xL xR + mk yl yr yL yR =
  mk (xl ⊕ yl) (xr ⊕ yr) (addL xL xR yL yR) (addR xL xR yL yR) := rfl

def left_moves_add_mk {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
  (mk xl xr xL xR + mk yl yr yL yR).left_moves = ((mk xl xr xL xR).left_moves ⊕ (mk yl yr yL yR).left_moves) :=
rfl
def right_moves_add_mk {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
  (mk xl xr xL xR + mk yl yr yL yR).right_moves = ((mk xl xr xL xR).right_moves ⊕ (mk yl yr yL yR).right_moves) :=
rfl

def left_moves_add {x y : pgame} : (x + y).left_moves ≃ (x.left_moves ⊕ y.left_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end
def right_moves_add {x y : pgame} : (x + y).right_moves ≃ (x.right_moves ⊕ y.right_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) = (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x y : pgame} {i} :
  (x + y).move_left (left_moves_add.inv_fun $ sum.inl i) = x.move_left i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) = (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x y : pgame} {i} :
  (x + y).move_right (right_moves_add.inv_fun $ sum.inl i) = x.move_right i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr {x y : pgame} {i} :
  (x + y).move_left (left_moves_add.inv_fun $ sum.inr i) = x + y.move_left i :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr {x y : pgame} {i} :
  (x + y).move_right (right_moves_add.inv_fun $ sum.inr i) = x + y.move_right i :=
begin
  cases x, cases y,
  refl,
end

instance : has_sub pgame := ⟨λ x y, x + -y⟩

inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π (x y : pgame) (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), relabelling (x.move_right (R.symm j)) (y.move_right j)) → relabelling x y


@[refl] def relabelling.refl : Π (x : pgame), relabelling x x
| (mk xl xr xL xR) :=
  relabelling.mk (mk xl xr xL xR) (mk xl xr xL xR) (equiv.refl _) (equiv.refl _)
    (λ i, relabelling.refl _) (λ j, relabelling.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

@[symm] def relabelling.symm : Π {x y : pgame}, relabelling x y → relabelling y x
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  refine relabelling.mk _ _ L_equiv.symm R_equiv.symm _ _,
  intro i,
  simpa using (L_relabelling (L_equiv.symm i)).symm,
  intro j,
  simpa using (R_relabelling (R_equiv j)).symm,
end

-- TODO trans for relabelling?

theorem le_of_relabelling : Π {x y : pgame} (r : relabelling x y), x ≤ y
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  rw le_def,
  fsplit,
  { intro i,
    right,
    use (L_equiv.to_fun i),
    dsimp,
    exact le_of_relabelling (L_relabelling i) },
  { intro j,
    left,
    use (R_equiv.inv_fun j),
    dsimp,
    exact le_of_relabelling (R_relabelling j) },
end

theorem ge_of_relabelling {x y : pgame} (r : relabelling x y) : x ≥ y :=
le_of_relabelling r.symm

def neg_add_relabelling : Π (x y : pgame), relabelling (-(x + y)) (-x + -y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  fsplit,
  refl,
  refl,
  { intro j, dsimp, change xr ⊕ yr at j,
    cases j,
    dsimp,
    exact neg_add_relabelling (xR j) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yR j), },
  { intro i, dsimp, change xl ⊕ yl at i,
    cases i,
    dsimp,
    exact neg_add_relabelling (xL i) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yL i), },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
le_of_relabelling (neg_add_relabelling x y)
theorem neg_add_ge {x y : pgame} : -(x + y) ≥ -x + -y :=
ge_of_relabelling (neg_add_relabelling x y)

-- theorem le_iff_sub_le_zero {x y : pgame} : x ≤ y ↔ x - y ≤ 0 := sorry
-- theorem le_iff_zero_le_sub {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry

theorem add_le_zero_of_le_zero : Π {x y : pgame} (hx : x ≤ 0) (hy : y ≤ 0), x + y ≤ 0
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  intros hx hy,
  rw le_zero,
  intro i,
  change xl ⊕ yl at i, -- FIXME dsimp should do this
  cases i,
  { use right_moves_add.inv_fun (sum.inl (right_response hx i)),
    simp,
    have rs := right_response_spec hx i,
    dsimp,
    simp,
    exact add_le_zero_of_le_zero rs hy, },
  { fsplit,
    change right_moves (mk xl xr xL xR + move_left (mk yl yr yL yR) i),
    use right_moves_add.inv_fun (sum.inr (right_response hy i)),
    simp,
    have rs := right_response_spec hy i,
    dsimp,
    simp,
    exact add_le_zero_of_le_zero hx rs, },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_add_of_zero_le : Π {x y : pgame} (hx : 0 ≤ x) (hy : 0 ≤ y), 0 ≤ x + y :=
begin
  intros x y,
  repeat { rw zero_le_iff_neg_le_zero },
  intros hx hy,
  transitivity,
  exact neg_add_le,
  solve_by_elim [add_le_zero_of_le_zero],
end

-- This is is just a temporary test to check pgame_wf_tac is working.
example {xl xr xL xR yl yr yL yR zl zr} {zL : zl → pgame} {zR} {i : zl} :
  has_well_founded.r
    (⟨mk xl xr xL xR, ⟨mk yl yr yL yR, zL i⟩⟩ : Σ' (g : pgame), Σ' (h : pgame), pgame)
    (⟨mk xl xr xL xR, ⟨mk yl yr yL yR, mk zl zr zL zR⟩⟩ : Σ' (g : pgame), Σ' (h : pgame), pgame) :=
begin
  -- apply psigma.lex.right,
  -- apply psigma.lex.right,
  -- apply r.left',
  pgame_wf_tac
end

theorem le_add_right : Π {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  intros h,
  rw le_def,
  fsplit,
  { -- if left plays first
    intros i,
    change xl ⊕ zl at i,
    cases i,
    { -- either they play in x
      rw le_def at h,
      cases h,
      have t := h_left i,
      rcases t with ⟨j, jh⟩ | ⟨i, ih⟩,
      { left,
        use right_moves_add.inv_fun (sum.inl j),
        dsimp,
        simp,
        exact le_add_right jh },
      { right,
        use left_moves_add.inv_fun (sum.inl i),
        dsimp,
        simp,
        exact le_add_right ih, },
      },
    { -- or play in z
      right,
      use left_moves_add.inv_fun (sum.inr i),
      dsimp,
      simp,
      exact le_add_right h,
    }, },
  { -- if right plays first
    intros j,
    change yr ⊕ zr at j,
    cases j,
    { -- either they play in y
      rw le_def at h,
      cases h,
      have t := h_right j,
      rcases t with ⟨j, jh⟩ | ⟨i, ih⟩,
      { left,
        use right_moves_add.inv_fun (sum.inl j),
        dsimp,
        simp,
        exact le_add_right jh },
      { right,
        use left_moves_add.inv_fun (sum.inl i),
        dsimp,
        simp,
        exact le_add_right ih, },
      },
    { -- or play in z
      left,
      use right_moves_add.inv_fun (sum.inr j),
      dsimp,
      simp,
      exact le_add_right h,
    }
  }
end
using_well_founded { dec_tac := pgame_wf_tac }


/-- The pre-surreal number `ω`. (In fact all ordinals have surreal
  representatives.) -/
def omega : pgame := ⟨ulift ℕ, pempty, λ n, ↑n.1, pempty.elim⟩

end pgame

local infix ` ≈ ` := pgame.equiv

instance pgame.setoid : setoid pgame :=
⟨λ x y, x ≈ y,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by equivalence so that
  the ordering becomes a total order. -/
def game := quotient pgame.setoid

open pgame

namespace game

/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy))

/-- The relation `x < y` on games. -/
def lt : game → game → Prop :=
quotient.lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : game}, ¬ le x y ↔ lt y x :=
by rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩; exact not_le

end game
