/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import algebraic_geometry.projective_spectrum.topology
import topology.sheaves.local_predicate
import ring_theory.localization.at_prime
import algebraic_geometry.locally_ringed_space

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `src/algebraic_geometry/topology.lean`, we have given a topology on `projective_spectrum 𝒜`; in
this file we will construct a sheaf on `projective_spectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `projective_spectrum.Top`.

## Main definitions and results
* `projective_spectrum.Top`: the topological space of `projective_spectrum 𝒜` endowed with the
  zariski topology
* `algebraic_geometry.projective_spectrum.structure_sheaf.homogeneous_localization`: given `x` in
  `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ` (`A` localized
  at prime `x`) where the numerator and denominator have same grading.

Then we define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, homogeneous_localization x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction`: the predicate that
  a dependent function is locally expressible as ration of two elements of the same grading.
* `algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, homogeneous_localization x`.
* `algebraic_geometry.Proj.structure_sheaf`: the sheaf with `U ↦ sections_subring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `algebraic_geometry.homogeneous_localization.is_local`: for any `x : projective_spectrum 𝒜`,
  `homogeneous_localization x` is a local ring.
* `algebraic_geometry.Proj.stalk_iso'`: for any `x : projective_spectrum 𝒜`, the stalk of
  `Proj.structure_sheaf` at `x` is isomorphic to `homogeneous_localization x`.
* `algebraic_geometry.Proj.to_LocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

local notation `at ` x := localization.at_prime x.as_homogeneous_ideal.to_ideal

open Top topological_space category_theory opposite

/--
The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def projective_spectrum.Top : Top := Top.of (projective_spectrum 𝒜)

namespace projective_spectrum.structure_sheaf

namespace homogeneous_localization

open set_like.graded_monoid submodule

variables {𝒜} (x : projective_spectrum.Top 𝒜)

/--
If `x` is a point in `Proj 𝒜`, then `y ∈ Aₓ` is said to satisfy `num_denom_same_deg` if and only if
`y = a / b` where `a` and `b` are both in `𝒜 i` for some `i`.
-/
@[nolint has_inhabited_instance]
structure num_denom_same_deg :=
(deg : ℕ)
(num denom : 𝒜 deg)
(denom_not_mem : (denom : A) ∉ x.as_homogeneous_ideal)

@[ext] lemma ext {c1 c2 : num_denom_same_deg x} (hdeg : c1.deg = c2.deg)
  (hnum : (c1.num : A) = c2.num) (hdenom : (c1.denom : A) = c2.denom) :
  c1 = c2 :=
begin
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩,
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩,
  dsimp only [subtype.coe_mk] at *,
  simp only,
  exact ⟨hdeg, by subst hdeg; subst hnum, by subst hdeg; subst hdenom⟩,
end

instance : has_one (num_denom_same_deg x) :=
{ one :=
  { deg := 0,
    num := ⟨1, one_mem⟩,
    denom := ⟨1, one_mem⟩,
    denom_not_mem := λ rid, x.is_prime.ne_top $ (ideal.eq_top_iff_one _).mpr rid } }

@[simp] lemma deg_one : (1 : num_denom_same_deg x).deg = 0 := rfl
@[simp] lemma num_one : ((1 : num_denom_same_deg x).num : A) = 1 := rfl
@[simp] lemma denom_one : ((1 : num_denom_same_deg x).denom : A) = 1 := rfl

instance : has_zero (num_denom_same_deg x) :=
{ zero :=
  { deg := 0,
    num := 0,
    denom := ⟨1, one_mem⟩,
    denom_not_mem := λ r, x.is_prime.ne_top $ (ideal.eq_top_iff_one _).mpr r } }

@[simp] lemma deg_zero : (0 : num_denom_same_deg x).deg = 0 := rfl
@[simp] lemma num_zero : (0 : num_denom_same_deg x).num = 0 := rfl
@[simp] lemma denom_zero : ((0 : num_denom_same_deg x).denom : A) = 1 := rfl

instance : has_mul (num_denom_same_deg x) :=
{ mul := λ p q,
  { deg := p.deg + q.deg,
    num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩,
    denom := ⟨p.denom * q.denom, mul_mem p.denom.prop q.denom.prop⟩,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) p.denom_not_mem q.denom_not_mem } }

lemma deg_mul (c1 c2 : num_denom_same_deg x) : (c1 * c2).deg = c1.deg + c2.deg := rfl
lemma num_mul (c1 c2 : num_denom_same_deg x) : ((c1 * c2).num : A) = c1.num * c2.num := rfl
lemma denom_mul (c1 c2 : num_denom_same_deg x) : ((c1 * c2).denom : A) = c1.denom * c2.denom := rfl

instance : has_add (num_denom_same_deg x) :=
{ add := λ c1 c2,
  { deg := c1.deg + c2.deg,
    num := ⟨c1.denom * c2.num + c2.denom * c1.num,
      add_mem _ (mul_mem c1.denom.2 c2.num.2)
        (add_comm c2.deg c1.deg ▸ mul_mem c2.denom.2 c1.num.2)⟩,
    denom := ⟨c1.denom * c2.denom, mul_mem c1.denom.2 c2.denom.2⟩,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem } }

lemma deg_add (c1 c2 : num_denom_same_deg x) : (c1 + c2).deg = c1.deg + c2.deg := rfl
lemma num_add (c1 c2 : num_denom_same_deg x) :
  ((c1 + c2).num : A) = c1.denom * c2.num + c2.denom * c1.num := rfl
lemma denom_add (c1 c2 : num_denom_same_deg x) :
  ((c1 + c2).denom : A) = c1.denom * c2.denom := rfl

instance : has_neg (num_denom_same_deg x) :=
{ neg := λ c, ⟨c.deg, ⟨-c.num, neg_mem _ c.num.2⟩, c.denom, c.denom_not_mem⟩ }

lemma deg_neg (c : num_denom_same_deg x) : (-c).deg = c.deg := rfl
lemma num_neg (c : num_denom_same_deg x) : ((-c).num : A) = -c.num := rfl
lemma denom_neg (c : num_denom_same_deg x) : ((-c).denom : A) = c.denom := rfl

instance : comm_monoid (num_denom_same_deg x) :=
{ one := 1,
  mul := (*),
  mul_assoc := λ c1 c2 c3, ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _),
  one_mul := λ c, ext _ (zero_add _) (one_mul _) (one_mul _),
  mul_one := λ c, ext _ (add_zero _) (mul_one _) (mul_one _),
  mul_comm := λ c1 c2, ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _) }

instance : has_pow (num_denom_same_deg x) ℕ :=
{ pow := λ c n, ⟨n • c.deg, ⟨c.num ^ n, pow_mem n c.num.2⟩, ⟨c.denom ^ n, pow_mem n c.denom.2⟩,
    begin
      cases n,
      { simp only [pow_zero],
        exact λ r, x.is_prime.ne_top $ (ideal.eq_top_iff_one _).mpr r, },
      { exact λ r, c.denom_not_mem $ (x.is_prime.pow_mem_iff_mem n.succ (nat.zero_lt_succ _)).mp r }
    end⟩ }

lemma deg_pow (c : num_denom_same_deg x) (n : ℕ) : (c ^ n).deg = n • c.deg := rfl
lemma num_pow (c : num_denom_same_deg x) (n : ℕ) : ((c ^ n).num : A) = c.num ^ n := rfl
lemma denom_pow (c : num_denom_same_deg x) (n : ℕ) : ((c ^ n).denom : A) = c.denom ^ n := rfl

instance : has_scalar ℤ (num_denom_same_deg x) :=
{ smul := λ m c, ⟨c.deg, ⟨m • c.num, begin
  rw [zsmul_eq_mul],
    suffices : (m : A) ∈ 𝒜 0,
    { convert mul_mem this c.num.2,
      rw zero_add, },
    { induction m using int.induction_on with m ih m ih,
      { exact zero_mem _ },
      { exact add_mem _ ih one_mem, },
      { push_cast at ih ⊢,
        exact sub_mem _ ih one_mem, } },
  end⟩, c.denom, c.denom_not_mem⟩ }

lemma deg_zsmul (c : num_denom_same_deg x) (m : ℤ) : (m • c).deg = c.deg := rfl
lemma num_zsmul (c : num_denom_same_deg x) (m : ℤ) : ((m • c).num : A) = m • c.num := rfl
lemma denom_zsmul (c : num_denom_same_deg x) (m : ℤ) : ((m • c).denom : A) = c.denom := rfl

instance nat_scalar : has_scalar ℕ (num_denom_same_deg x) :=
{ smul := λ m c, (m : ℤ) • c }

def num_denom_same_deg.embedding (p : num_denom_same_deg x) : at x :=
localization.mk p.num ⟨p.denom, p.denom_not_mem⟩

def homogeneous_localization : Type* := quotient (setoid.ker $ num_denom_same_deg.embedding x)

variable {x}
def homogeneous_localization.val (y : homogeneous_localization x) : at x :=
quotient.lift_on' y (num_denom_same_deg.embedding x) $ λ _ _, id

variable (x)
lemma homogeneous_localization.val_injective :
  function.injective (@homogeneous_localization.val _ _ _ _ _ 𝒜 _ x) :=
λ a b, quotient.rec_on_subsingleton₂' a b $ λ a b h, quotient.sound' h

instance homogeneous_localization.has_pow : has_pow (homogeneous_localization x) ℕ :=
{ pow := λ z n, (quotient.map' (^ n)
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_pow, denom_pow],
      convert congr_arg (λ z, z ^ n) h;
      erw localization.mk_pow;
      refl,
    end) : homogeneous_localization x → homogeneous_localization x) z }

instance : has_scalar ℤ (homogeneous_localization x) :=
{ smul := λ m, quotient.map' ((•) m)
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_zsmul, denom_zsmul],
      convert congr_arg (λ z, m • z) h;
      rw [zsmul_eq_mul, zsmul_eq_mul, show (m : at x) = localization.mk m 1, begin
        induction m using int.induction_on with n ih n ih,
        { erw localization.mk_zero _, refl, },
        { push_cast,
          erw [ih, ← localization.mk_one, localization.add_mk, one_mul, one_mul, add_comm, one_mul],
          refl, },
        { push_cast at ih ⊢,
          erw [ih, ← localization.mk_one, sub_eq_add_neg, localization.neg_mk, localization.add_mk,
            mul_one, one_mul, one_mul, add_comm, ← sub_eq_add_neg], },
      end, localization.mk_mul, one_mul];
      refl,
    end) }

instance homogeneous_localization.nat_scalar : has_scalar ℕ (homogeneous_localization x) :=
{ smul := λ n z, (n : ℤ) • z }

instance : has_neg (homogeneous_localization x) :=
{ neg := quotient.map' has_neg.neg
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_neg, denom_neg, ←localization.neg_mk],
      exact congr_arg (λ c, -c) h
    end) }

instance : has_add (homogeneous_localization x) :=
{ add := quotient.map₂' (+) (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _)
    c3 c4 (h' : localization.mk _ _ = localization.mk _ _), begin
    change localization.mk _ _ = localization.mk _ _,
    simp only [num_add, denom_add, ←localization.add_mk],
    convert congr_arg2 (+) h h';
    erw [localization.add_mk];
    refl,
  end) }

instance : has_sub (homogeneous_localization x) :=
{ sub := λ z1 z2, z1 + (-z2) }

instance : has_mul (homogeneous_localization x) :=
{ mul := quotient.map₂' (*) (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _)
    c3 c4 (h' : localization.mk _ _ = localization.mk _ _), begin
    change localization.mk _ _ = localization.mk _ _,
    simp only [num_mul, denom_mul],
    convert congr_arg2 (*) h h';
    erw [localization.mk_mul];
    refl,
  end) }

instance : has_one (homogeneous_localization x) :=
{ one := quotient.mk' 1 }

instance : has_zero (homogeneous_localization x) :=
{ zero := quotient.mk' 0 }

lemma homogeneous_localization.zero_eq :
  (0 : homogeneous_localization x) = quotient.mk' 0 :=
rfl

lemma homogeneous_localization.one_eq :
  (1 : homogeneous_localization x) = quotient.mk' 1 :=
rfl

variable {x}
lemma zero_val : (0 : homogeneous_localization x).val= 0 :=
begin
  rw [homogeneous_localization.zero_eq, homogeneous_localization.val, quotient.lift_on'_mk'],
  change localization.mk _ _ = _,
  convert localization.mk_zero _,
end

lemma one_val : (1 : homogeneous_localization x).val= 1 :=
begin
  rw [homogeneous_localization.one_eq, homogeneous_localization.val, quotient.lift_on'_mk'],
  change localization.mk _ _ = _,
  simp only [num_one, denom_one],
  convert localization.mk_self _,
  refl,
end

lemma add_val (y1 y2 : homogeneous_localization x) :
  (y1 + y2).val = y1.val + y2.val :=
begin
  induction y1 using quotient.induction_on,
  induction y2 using quotient.induction_on,
  unfold homogeneous_localization.val has_add.add,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = localization.mk _ _ + localization.mk _ _,
  dsimp only,
  rw [localization.add_mk],
  refl,
end

lemma mul_val (y1 y2 : homogeneous_localization x) :
  (y1 * y2).val = y1.val * y2.val :=
begin
  induction y1 using quotient.induction_on,
  induction y2 using quotient.induction_on,
  unfold homogeneous_localization.val has_mul.mul,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = localization.mk _ _ * localization.mk _ _,
  dsimp only,
  rw [localization.mk_mul],
  refl,
end

lemma neg_val (y : homogeneous_localization x) :
  (-y).val = -y.val :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_neg.neg,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = - localization.mk _ _,
  dsimp only,
  rw [localization.neg_mk],
  refl,
end

lemma sub_val (y1 y2 : homogeneous_localization x) :
  (y1 - y2).val = y1.val - y2.val :=
begin
  rw [show y1 - y2 = y1 + (-y2), from rfl, add_val, neg_val],
  refl,
end

lemma nsmul_val (y : homogeneous_localization x) (n : ℕ) :
  (n • y).val = n • y.val :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_scalar.smul,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = n • localization.mk _ _,
  dsimp only,
  rw [nsmul_eq_mul, show (n : at x) = localization.mk n 1, begin
    induction n with n ih,
    { erw localization.mk_zero, refl, },
    { rw [nat.succ_eq_add_one],
      push_cast,
      rw [ih, ← localization.mk_one, localization.add_mk, mul_one, one_mul, add_comm],
      congr' 1,
      erw one_mul,
      refl, },
  end, localization.mk_mul, one_mul],
  congr' 1,
  simp only [← subtype.val_eq_coe],
  rw [show ↑n * y.num.val = ↑(n : ℤ) * y.num.val, by norm_cast, ← zsmul_eq_mul],
  refl,
end

lemma zsmul_val (y : homogeneous_localization x) (n : ℤ) :
  (n • y).val = n • y.val :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_scalar.smul,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = n • localization.mk _ _,
  dsimp only,
  rw [zsmul_eq_mul, show (n : at x) = localization.mk n 1, begin
    induction n using int.induction_on with n ih n ih,
    { erw localization.mk_zero, refl, },
    { push_cast,
      erw [ih, ← localization.mk_one, localization.add_mk, mul_one, one_mul, add_comm, one_mul],
      congr' 1, },
    { push_cast at ih ⊢,
      rw neg_eq_iff_neg_eq at ih,
      erw [show -(n : at x) - 1 = - (n + 1), by ring, ← ih,
        show -(n : A) - 1 = - (n + 1), by ring, localization.neg_mk, neg_neg, ← localization.mk_one,
        localization.add_mk, one_mul, mul_one, localization.neg_mk, one_mul, add_comm], },
  end, localization.mk_mul, one_mul],
  congr' 1,
  simp only [← subtype.val_eq_coe],
  rw [← zsmul_eq_mul],
  refl,
end

lemma pow_val (y : homogeneous_localization x) (n : ℕ) :
  (y ^ n).val = y.val ^ n :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_pow.pow,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = (localization.mk _ _) ^ n,
  rw localization.mk_pow,
  dsimp only,
  congr' 1,
end

instance : comm_ring (homogeneous_localization x) :=
(homogeneous_localization.val_injective x).comm_ring _ zero_val one_val add_val mul_val neg_val
  sub_val nsmul_val zsmul_val pow_val
end homogeneous_localization

namespace homogeneous_localization
variables {𝒜} {x : projective_spectrum.Top 𝒜}

/-- numerator of an element in `homogeneous_localization x`-/
def homogeneous_localization.num (f : homogeneous_localization x) : A :=
(quotient.out' f).num

/-- denominator of an element in `homogeneous_localization x`-/
def homogeneous_localization.denom (f : homogeneous_localization x) : A :=
(quotient.out' f).denom

/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def homogeneous_localization.deg (f : homogeneous_localization x) : ℕ :=
(quotient.out' f).deg

lemma homogeneous_localization.denom_not_mem (f : homogeneous_localization x) :
  f.denom ∉ x.as_homogeneous_ideal :=
(quotient.out' f).denom_not_mem

lemma homogeneous_localization.num_mem (f : homogeneous_localization x) : f.num ∈ 𝒜 f.deg :=
(quotient.out' f).num.2

lemma homogeneous_localization.denom_mem (f : homogeneous_localization x) : f.denom ∈ 𝒜 f.deg :=
(quotient.out' f).denom.2

lemma homogeneous_localization.eq' (f : homogeneous_localization x) :
  f = quotient.mk' (quotient.out' f) :=
(quotient.out_eq' f).symm

lemma homogeneous_localization.eq_num_div_denom (f : homogeneous_localization x) :
  f.val = localization.mk f.num ⟨f.denom, f.denom_not_mem⟩ :=
begin
  have := (quotient.out_eq' f).symm,
  apply_fun homogeneous_localization.val at this,
  rw this,
  unfold homogeneous_localization.val,
  simp only [quotient.lift_on'_mk'],
  refl,
end

lemma ext_iff_val (f g : homogeneous_localization x) : f = g ↔ f.val = g.val :=
{ mp := λ h, h ▸ rfl,
  mpr := λ h, begin
    induction f using quotient.induction_on,
    induction g using quotient.induction_on,
    rw quotient.eq,
    unfold homogeneous_localization.val at h,
    simp only [quotient.lift_on'_mk] at h,
    exact h,
  end }

end homogeneous_localization

end projective_spectrum.structure_sheaf

end algebraic_geometry
