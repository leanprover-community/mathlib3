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
(denom_not_mem : denom.1 ∉ x.as_homogeneous_ideal)

@[ext] lemma ext {c1 c2 : num_denom_same_deg x} (hdeg : c1.deg = c2.deg)
  (hnum : c1.num.1 = c2.num.1) (hdenom : c1.denom.1 = c2.denom.1) :
  c1 = c2 :=
begin
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩,
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩,
  dsimp only at *,
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
    num := ⟨c1.denom.1 * c2.num.1 + c2.denom.1 * c1.num.1,
      add_mem _ (mul_mem c1.denom.2 c2.num.2)
        (add_comm c2.deg c1.deg ▸ mul_mem c2.denom.2 c1.num.2)⟩,
    denom := ⟨c1.denom.1 * c2.denom.1, mul_mem c1.denom.2 c2.denom.2⟩,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem } }

lemma deg_add (c1 c2 : num_denom_same_deg x) : (c1 + c2).deg = c1.deg + c2.deg := rfl
lemma num_add (c1 c2 : num_denom_same_deg x) :
  ((c1 + c2).num : A) = c1.denom * c2.num + c2.denom * c1.num := rfl
lemma denom_add (c1 c2 : num_denom_same_deg x) :
  ((c1 + c2).denom : A) = c1.denom * c2.denom := rfl

instance : has_neg (num_denom_same_deg x) :=
{ neg := λ c, ⟨c.deg, ⟨-c.num.1, neg_mem _ c.num.2⟩, c.denom, c.denom_not_mem⟩ }

lemma deg_neg (c : num_denom_same_deg x) : (-c).deg = c.deg := rfl
lemma num_neg (c : num_denom_same_deg x) : (-c).num.1 = -c.num.1 := rfl
lemma denom_neg (c : num_denom_same_deg x) : (-c).denom.1 = c.denom.1 := rfl

instance : comm_monoid (num_denom_same_deg x) :=
{ one := 1,
  mul := (*),
  mul_assoc := λ c1 c2 c3, ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _),
  one_mul := λ c, ext _ (zero_add _) (one_mul _) (one_mul _),
  mul_one := λ c, ext _ (add_zero _) (mul_one _) (mul_one _),
  mul_comm := λ c1 c2, ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _) }

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

instance : has_pow (homogeneous_localization x) ℕ :=
{ pow := λ z n, quotient.lift_on' z
    (λ c, @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x)
      { deg := n • c.deg,
        num := ⟨c.num.1 ^ n, pow_mem n c.num.2⟩,
        denom := ⟨c.denom.1 ^ n, pow_mem n c.denom.2⟩,
        denom_not_mem := λ r, begin
          dsimp only at r,
          cases n,
          { erw [pow_zero, ← ideal.eq_top_iff_one] at r,
            exact x.is_prime.ne_top r, },
          { apply c.denom_not_mem ((x.is_prime.pow_mem_iff_mem n.succ (nat.zero_lt_succ _)).mp r) }
        end }) $ λ y1 y2 (h : localization.mk _ _ = localization.mk _ _), begin
          rw quotient.eq,
          change localization.mk _ _ = localization.mk _ _,
          simp only [← subtype.val_eq_coe] at h ⊢,
          erw [← localization.mk_pow n y1.num.1 (⟨y1.denom, y1.denom_not_mem⟩ :
            x.as_homogeneous_ideal.to_ideal.prime_compl),
            ← localization.mk_pow n y2.num.1 (⟨y2.denom, y2.denom_not_mem⟩ :
            x.as_homogeneous_ideal.to_ideal.prime_compl), h],
          refl,
        end }

instance : has_scalar ℤ (homogeneous_localization x) :=
{ smul := λ m z, quotient.lift_on' z
    (λ c, @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x)
      { deg := c.deg,
        num := ⟨m • c.num.1, begin
          rw zsmul_eq_mul,
          suffices : (m : A) ∈ 𝒜 0,
          { simpa only [zero_add] using mul_mem this c.num.2 },
          { induction m using int.induction_on with m ih m ih,
            { exact zero_mem _ },
            { exact add_mem _ ih one_mem, },
            { push_cast at ih ⊢,
              exact sub_mem _ ih one_mem, } },
        end⟩,
        denom := c.denom,
        denom_not_mem := c.denom_not_mem }) $
    λ y1 y2 (h : localization.mk _ _ = localization.mk _ _), begin
      rw quotient.eq,
      change localization.mk _ _ = localization.mk _ _,
      simp only [← subtype.val_eq_coe] at h ⊢,
      erw [show (localization.mk (m • y1.num.val) ⟨y1.denom.1, y1.denom_not_mem⟩ : at x) =
        localization.mk m 1 * localization.mk y1.num.1 ⟨y1.denom.1, y1.denom_not_mem⟩,
          by rw [localization.mk_mul _ _, one_mul, zsmul_eq_mul],
        show (localization.mk (m • y2.num.val) ⟨y2.denom.1, y2.denom_not_mem⟩ : at x) =
        localization.mk m 1 * localization.mk y2.num.1 ⟨y2.denom.1, y2.denom_not_mem⟩,
          by rw [localization.mk_mul _ _, one_mul, zsmul_eq_mul], h],
      refl,
    end }

instance nat_scalar : has_scalar ℕ (homogeneous_localization x) :=
{ smul := λ n z, (n : ℤ) • z }

instance : has_neg (homogeneous_localization x) :=
{ neg := λ z, quotient.lift_on' z
    (λ c, @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) (-c)) $
    λ y1 y2 (h : localization.mk _ _ = localization.mk _ _), begin
      rw quotient.eq,
      change localization.mk _ _ = localization.mk _ _,
      simp only [← subtype.val_eq_coe] at h ⊢,
      erw [← localization.neg_mk, ← localization.neg_mk],
      congr' 1,
    end }

instance : has_add (homogeneous_localization x) :=
{ add := λ z1 z2, quotient.lift_on₂' z1 z2
    (λ c1 c2, @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) (c1 + c2)) $
    λ c1 c2 c1' c2' (h1 : localization.mk _ _ = localization.mk _ _)
      (h2 : localization.mk _ _ = localization.mk _ _), begin
        rw quotient.eq,
        change localization.mk _ _ = localization.mk _ _,
        simp only [num_add, denom_add],
        have h3 := congr_arg2 (+) h1 h2,
        erw [localization.add_mk, localization.add_mk] at h3,
        convert h3,
      end }

instance : has_sub (homogeneous_localization x) :=
{ sub := λ z1 z2, z1 + (-z2) }

instance : has_mul (homogeneous_localization x) :=
{ mul := λ z1 z2, quotient.lift_on₂' z1 z2
    (λ c1 c2, @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) (c1 * c2)) $
    λ c1 c2 c1' c2' (h1 : localization.mk _ _ = localization.mk _ _)
      (h2 : localization.mk _ _ = localization.mk _ _), begin
        rw quotient.eq,
        change localization.mk _ _ = localization.mk _ _,
        simp only [num_mul, denom_mul],
        have h3 := congr_arg2 (*) h1 h2,
        erw [localization.mk_mul, localization.mk_mul] at h3,
        convert h3,
      end  }

instance : has_one (homogeneous_localization x) :=
{ one := @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) 1 }

instance : has_zero (homogeneous_localization x) :=
{ zero := @@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) 0 }

lemma homogeneous_localization.zero_eq :
  (0 : homogeneous_localization x) =@@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) 0 :=
rfl

lemma homogeneous_localization.one_eq :
  (1 : homogeneous_localization x) =@@quotient.mk (setoid.ker $ num_denom_same_deg.embedding x) 1 :=
rfl

variable {x}
lemma zero_val : (0 : homogeneous_localization x).val= 0 :=
begin
  rw [homogeneous_localization.zero_eq, homogeneous_localization.val, quotient.lift_on'_mk],
  change localization.mk _ _ = _,
  convert localization.mk_zero _,
end

lemma one_val : (1 : homogeneous_localization x).val= 1 :=
begin
  rw [homogeneous_localization.one_eq, homogeneous_localization.val, quotient.lift_on'_mk],
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

lemma pow_val (n : ℕ) (y : homogeneous_localization x) :
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

-- def homogeneous_localization := set.range (embedding x)

-- instance : comm_ring (homogeneous_localization x) := sorry

#exit
attribute [simp] num_denom_same_deg.eq

variable (x)
/--
Auxiliary definition of `homogeneous_localization`: its underlying set.
-/
def carrier : set (at x) :=
{y | nonempty (num_denom_same_deg y)}

variable {x}
lemma one_mem' : (1 : at x) ∈ carrier x := nonempty.intro
{ num := 1,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := one_mem,
  denom_mem := one_mem,
  eq := by simp }

lemma zero_mem' : (0 : at x) ∈ carrier x := nonempty.intro
{ num := 0,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := zero_mem _,
  denom_mem := one_mem,
  eq := by simp }

lemma mul_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 * y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.num * c2.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := mul_mem c1.num_mem c2.num_mem,
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.mk_mul] }
end

lemma add_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 + y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.denom * c2.num + c2.denom * c1.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := add_mem _ (mul_mem c1.denom_mem c2.num_mem)
      (add_comm c2.deg c1.deg ▸ mul_mem c2.denom_mem c1.num_mem),
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.add_mk] }
end

lemma neg_mem' {y} (hy : y ∈ carrier x) : -y ∈ carrier x :=
match hy with
| ⟨c⟩ := nonempty.intro
  { num := -c.num,
    denom := c.denom,
    denom_not_mem := c.denom_not_mem,
    deg := c.deg,
    num_mem := neg_mem _ c.num_mem,
    denom_mem := c.denom_mem,
    eq := by simp only [← c.eq, localization.neg_mk] }
end

end homogeneous_localization

section
variable {𝒜}
open homogeneous_localization

/-- given `x` in `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ`
(`A` localized at prime `x`) where the numerator and denominator have same grading. -/
@[derive [comm_ring], nolint has_inhabited_instance]
def homogeneous_localization (x : projective_spectrum.Top 𝒜) : Type* :=
subring.mk (carrier x) (λ _ _, mul_mem') one_mem' (λ _ _, add_mem') zero_mem'  (λ _, neg_mem')

end

namespace homogeneous_localization
variables {𝒜} {x : projective_spectrum.Top 𝒜}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : homogeneous_localization x) : A := (nonempty.some f.2).num
/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : homogeneous_localization x) : A := (nonempty.some f.2).denom
/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : homogeneous_localization x) : ℕ := (nonempty.some f.2).deg

lemma denom_not_mem (f : homogeneous_localization x) : f.denom ∉ x.as_homogeneous_ideal :=
(nonempty.some f.2).denom_not_mem

lemma num_mem (f : homogeneous_localization x) : f.num ∈ 𝒜 f.deg := (nonempty.some f.2).num_mem
lemma denom_mem (f : homogeneous_localization x) : f.denom ∈ 𝒜 f.deg :=
(nonempty.some f.2).denom_mem

lemma eq_num_div_denom (f : homogeneous_localization x) :
  f.1 = localization.mk f.num ⟨f.denom, f.denom_not_mem⟩ :=
(nonempty.some f.2).eq.symm

lemma val_add (f g : homogeneous_localization x) : (f + g).1 = f.val + g.val := rfl

lemma val_neg (f : homogeneous_localization x) : (-f).val = -f.val := rfl

lemma val_mul (f g : homogeneous_localization x) : (f * g).val = f.val * g.val := rfl

lemma val_sub (f g : homogeneous_localization x) : (f - g).val = f.val - g.val := rfl

lemma val_zero : (0 : homogeneous_localization x).val = localization.mk 0 1 :=
by rw localization.mk_zero; refl

lemma val_one : (1 : homogeneous_localization x).val = localization.mk 1 1 :=
by rw localization.mk_one; refl

lemma ext_iff_val (f g : homogeneous_localization x) : f = g ↔ f.1 = g.1:= subtype.ext_iff_val

end homogeneous_localization

end projective_spectrum.structure_sheaf

end algebraic_geometry
