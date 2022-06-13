import data.zmod.algebra
import field_theory.ratfunc
import algebraic_geometry.EllipticCurve

structure ShortEllipticCurve (R : Type*) [comm_ring R] extends to_long : EllipticCurve R :=
(a1_zero : to_long.a1 = 0)
(a2_zero : to_long.a2 = 0)
(a3_zero : to_long.a3 = 0)

section simps
variables {R : Type*} [comm_ring R] {E : ShortEllipticCurve R}

@[simp] lemma a1_zero : E.a1 = 0 := E.a1_zero
@[simp] lemma a2_zero : E.a2 = 0 := E.a2_zero
@[simp] lemma a3_zero : E.a3 = 0 := E.a3_zero

end simps

section points
variables {R : Type*} [comm_ring R] (E : EllipticCurve R) (S : Type*) [comm_ring S] [algebra R S]
open set
def EllipticCurve.points : Type* :=
{ XY : S × S //
  XY.2 ^ 2 + E.a1 • XY.1 * XY.2 + E.a3 • XY.2 = XY.1^3 + E.a2 • XY.1^2 + E.a4 • XY.1 + E.a6 • 1 }

def EllipticCurve.mk_point (val h) : EllipticCurve.points E S := subtype.mk val h
end points

section twist
universes u v
variables {R : Type u} {h : comm_ring R} (E : ShortEllipticCurve R) -- TODO linter for no [comm_ring]
variables {S : Type v} [comm_ring S] [algebra R S]

@[simp]
def ShortEllipticCurve.twist (D : Sˣ) : ShortEllipticCurve.{v} S :=
{ a1 := E.a1 • 1,
  a2 := E.a2 • 1,
  a3 := E.a3 • 1,
  a4 := E.a4 • D ^ 2,
  a6 := E.a6 • D ^ 3,
  disc_unit := E.disc_unit • D ^ 6,
  disc_unit_eq := begin
    simp [EllipticCurve.disc_aux, EllipticCurve.disc_unit_eq],
    simp [smul_pow, ← units.coe_pow],
    sorry,
  end,
  a1_zero := by simp,
  a2_zero := by simp,
  a3_zero := by simp }
end twist

section group_law
variables {R : Type*} [field R] (E : ShortEllipticCurve R)
variables (S : Type*) [field S] [algebra R S]

def add : option (E.to_long.points S) → option (E.to_long.points S) → option (E.to_long.points S)
| none P := P
| P none := P
| (some p1) (some p2) := some (let x3 := - p1.1.1 - p2.1.1 + ((p2.1.2 - p1.1.2) / (p2.1.1 - p1.1.1)) ^ 2 in
    E.to_long.mk_point S ⟨x3, (p2.1.2 - p1.1.2) / (p2.1.1 - p1.1.1) * (x3 - p1.1.1) + p1.1.2⟩ sorry)

def neg : option (E.to_long.points S) → option (E.to_long.points S)
| none := none
| (some p1) := some $ E.to_long.mk_point S ⟨p1.1.1, p1.1.2⟩ begin
  cases p1,
  simp [smul_mul_assoc, a1_zero] at *,
  rw a1_zero at p1_property,
  rw a2_zero at p1_property,
  rw a3_zero at p1_property,
  simpa using p1_property, end

instance : add_group (option (E.to_long.points S)) :=
{ add := add E S,
  add_assoc := sorry,
  zero := none,
  zero_add := λ a, begin cases a; refl end,
  add_zero := λ a, begin cases a; refl end,
  neg := neg E S,
  add_left_neg := sorry }

@[simp]
lemma neg_apply (x y : S) (h) : -(↑(E.to_long.mk_point S ⟨x, y⟩ h) : option _) = (↑(E.to_long.mk_point S ⟨x, -y⟩ (by simpa using h)) : option $ E.to_long.points S) :=
by simp [option.coe_def]; sorry

end group_law

namespace hasse

variables {p : ℕ} (h : 5 ≤ p) [fact p.prime] (E : ShortEllipticCurve (zmod p))
open finset
open_locale classical
noncomputable theory

open ratfunc

lemma D_nonzero : (X ^ 3 + E.to_long.a4 * X + E.to_long.a6 : ratfunc (zmod p)) ≠ 0 :=
begin
sorry  -- something with int_degree
end

def b : (E.twist (units.mk0 _ (D_nonzero E))).to_long.points (ratfunc (zmod p)) :=
EllipticCurve.mk_point _ _ ⟨(X ^ 3 + E.to_long.a4 * X + E.to_long.a6 : ratfunc (zmod p)) * X,
  (X ^ 3 + E.to_long.a4 * X + E.to_long.a6 : ratfunc (zmod p)) ^ 2⟩ begin
  set f : ratfunc (zmod p) := X ^ 3 + E.to_long.a4 * X + E.to_long.a6,
  simp,
  ring_nf,
  sorry -- looks right
end

include h

def step : (E.twist (units.mk0 _ (D_nonzero E))).to_long.points (ratfunc (zmod p)) :=
EllipticCurve.mk_point _ _ ⟨(X ^ 3 + E.to_long.a4 * X + E.to_long.a6 : ratfunc (zmod p)) * X ^ p,
  (X ^ 3 + E.to_long.a4 * X + E.to_long.a6 : ratfunc (zmod p)) ^ 2 *
  (X ^ 3 + E.to_long.a4 * X + E.to_long.a6) ^ ((p - 1) / 2)⟩ begin
  set f : ratfunc (zmod p) := X ^ 3 + E.to_long.a4 * X + E.to_long.a6,
  simp [mul_pow],
  simp [← pow_mul],
  ring_exp,
  rw (_ : (p - 1) / 2 * 2 = p),
  sorry
end

def P (n : ℤ) : option ((E.twist (units.mk0 _ (D_nonzero E))).to_long.points (ratfunc (zmod p))) :=
(b E) + n • step h E

@[simp]
lemma P_zero : P h E 0 = b E := by simp [P]
-- lemma P_one : d E 1 = 1 := sorry
.


def d (n : ℤ) : ℕ :=
polynomial.nat_degree
((P h E n).get_or_else (b E)).1.1.num

lemma d_zero : d h E 0 = p := begin
  simp [d],
end


lemma X_neg_one : ((P h E (-1)).get_or_else (b E)).1.1 =
  (X ^ 3 + E.a4 * X + E.a6) * ((X^3 + E.a4 * X + E.a6)^((p-1) / 2) + 1)^2 / ((X^p - X)^2) - (X^p + X) :=
begin
  simp [P, step, b],
end
-- =\frac{t^{2 p+1}+\text { a polynomial of degree at most2p }}{\left(t^{p}-t\right)^{2}}
-- lemma d_one : d E 1 = 1 := sorry

lemma lemma_1 : (d h E (-1) - d h E 0 - 1) = nat.card (E.to_long.points (zmod p)) - p := sorry
lemma fundamental_lemma (n : ℤ) : d h E (n - 1) + d h E (n + 1) = 2 * d h E n + 2 := sorry

lemma lemma_2 (n : ℤ) : (d h E n : ℤ) = n ^ 2 - ↑(d h E (-1) - d h E 0 - 1) * n + d h E 0 :=
begin
  cases n; simp,
  apply nat.strong_induction_on n,
  { intros n ih, simp },
  { simp },
end

theorem hasse : |(p : ℤ) - nat.card (E.to_long.points (zmod p))| ≤ 2 * p.sqrt :=
begin
  have := lemma_2 h E,
  simp_rw [lemma_1 h E] at this,
  sorry
end

end hasse

#lint
