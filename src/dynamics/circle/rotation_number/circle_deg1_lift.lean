import order.iterate
import algebra.iterate_hom
import topology.instances.real
import order.semiconj_Sup
import .to_mathlib

open filter set function (hiding commute)
open_locale topological_space classical

/-!
### Definition
-/

/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure circle_deg1_lift : Type :=
(to_fun : ℝ → ℝ)
(monotone' : monotone to_fun)
(map_add_one' : ∀ x, to_fun (x + 1) = to_fun x + 1)

namespace circle_deg1_lift

instance : has_coe_to_fun circle_deg1_lift := ⟨λ _, ℝ → ℝ, circle_deg1_lift.to_fun⟩

@[simp] lemma coe_mk (f h₁ h₂) : ⇑(mk f h₁ h₂) = f := rfl

variables (f g : circle_deg1_lift)

protected lemma monotone  : monotone f := f.monotone'

lemma strict_mono_iff_injective : strict_mono f ↔ injective f :=
f.monotone.strict_mono_iff_injective

@[simp] lemma map_add_one : ∀ x, f (x + 1) = f x + 1 := f.map_add_one'

@[simp] lemma map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm]

theorem coe_injective : injective (λ (f : circle_deg1_lift) x, f x) :=
assume ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h, by congr; exact h

@[simp, norm_cast] theorem coe_inj {f g : circle_deg1_lift} : (f : ℝ → ℝ) = g ↔ f = g :=
coe_injective.eq_iff

@[ext] theorem ext' {f g : circle_deg1_lift} (h : (f : ℝ → ℝ) = g) : f = g := coe_injective h

theorem ext_iff {f g : circle_deg1_lift} : f = g ↔ ∀ x, f x = g x :=
coe_inj.symm.trans funext_iff

theorem ext ⦃f g : circle_deg1_lift⦄ (h : ∀ x, f x = g x) : f = g := ext_iff.2 h

/-!
### Monoid structure
-/

instance : monoid circle_deg1_lift :=
{ mul := λ f g,
  { to_fun := f ∘ g,
    monotone' := f.monotone.comp g.monotone,
    map_add_one' := λ x, by simp [map_add_one] },
  one := ⟨id, monotone_id, λ _, rfl⟩,
  mul_one := λ f, ext' $ function.comp.right_id f,
  one_mul := λ f, ext' $ function.comp.left_id f,
  mul_assoc := λ f₁ f₂ f₃, ext' rfl }

instance : inhabited circle_deg1_lift := ⟨1⟩

@[simp, norm_cast] lemma coe_mul : ⇑(f * g) = f ∘ g := rfl

lemma mul_apply (x) : (f * g) x = f (g x) := rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : circle_deg1_lift) = id := rfl

lemma coe_pow : ∀ n : ℕ, ⇑(f^n) = (f^[n])
| 0 := rfl
| (n+1) := by {ext x, simp [coe_pow n, pow_succ'] }

lemma semiconj_by_iff_semiconj {f g₁ g₂ : circle_deg1_lift} :
  semiconj_by f g₁ g₂ ↔ semiconj f g₁ g₂ :=
ext_iff

lemma commute_iff_commute {f g : circle_deg1_lift} :
  commute f g ↔ function.commute f g :=
ext_iff

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `function.commute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/

lemma commute_nat_add (n : ℕ) : function.commute f ((+) n) :=
by simpa only [nsmul_one, add_left_iterate] using function.commute.iterate_right f.map_one_add n

lemma commute_add_nat (n : ℕ) : function.commute f (λ x, x + n) :=
by simp only [add_comm _ (n:ℝ), f.commute_nat_add n]

lemma commute_sub_nat (n : ℕ) : function.commute f (λ x, x - n) :=
by simpa only [sub_eq_add_neg] using
  (f.commute_add_nat n).inverses_right (equiv.add_right _).right_inv (equiv.add_right _).left_inv

lemma commute_add_int : ∀ n : ℤ, function.commute f (λ x, x + n)
| (n:ℕ) := f.commute_add_nat n
| -[1+n] := by simpa only [sub_eq_add_neg] using f.commute_sub_nat (n + 1)

lemma commute_int_add (n : ℤ) : function.commute f ((+) n) :=
by simpa only [add_comm _ (n:ℝ)] using f.commute_add_int n

lemma commute_sub_int (n : ℤ) : function.commute f (λ x, x - n) :=
by simpa only [sub_eq_add_neg] using
  (f.commute_add_int n).inverses_right (equiv.add_right _).right_inv (equiv.add_right _).left_inv

@[simp] lemma map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
f.commute_int_add m x

@[simp] lemma map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
f.commute_add_int m x

@[simp] lemma map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
f.commute_sub_int n x

@[simp] lemma map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
f.map_add_int x n

@[simp] lemma map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
f.map_int_add n x

@[simp] lemma map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
f.map_sub_int x n

@[simp] lemma map_sub_one (x : ℝ) : f (x - 1) = f x - 1 :=
by simpa only [nat.cast_one] using f.map_sub_nat x 1

lemma map_int_of_map_zero (n : ℤ) : f n = f 0 + n :=
by rw [← f.map_add_int, zero_add]

/-- Function `f x - x` is `1`-periodic, thus `f({x}) - {x} = f(x) - x` for all real `x`. -/
@[simp] lemma map_fract_sub_fract_eq (x : ℝ) :
  f (fract x) - fract x = f x - x :=
by rw [fract, f.map_sub_int, sub_sub_sub_cancel_right]

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/

lemma map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
calc f x ≤ f ⌈x⌉     : f.monotone $ le_ceil _
     ... = f 0 + ⌈x⌉ : f.map_int_of_map_zero _

lemma map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_le_of_map_zero (g 0)

lemma floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
calc ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ : floor_mono $ f.map_map_zero_le g
           ... = ⌊f 0⌋ + ⌈g 0⌉ : floor_add_int _ _

lemma ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
calc ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ : ceil_mono $ f.map_map_zero_le g
           ... = ⌈f 0⌉ + ⌈g 0⌉ : ceil_add_int _ _

lemma map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
calc f (g 0) ≤ f 0 + ⌈g 0⌉     : f.map_map_zero_le g
         ... < f 0 + (g 0 + 1) : add_lt_add_left (ceil_lt_add_one _) _
         ... = f 0 + g 0 + 1   : (add_assoc _ _ _).symm

lemma le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
calc f 0 + ⌊x⌋ = f ⌊x⌋ : (f.map_int_of_map_zero _).symm
           ... ≤ f x   : f.monotone $ floor_le _

lemma le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) := f.le_map_of_map_zero (g 0)

lemma le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
calc ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ : (floor_add_int _ _).symm
               ... ≤ ⌊f (g 0)⌋     : floor_mono $ f.le_map_map_zero g

lemma le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
calc ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ : (ceil_add_int _ _).symm
               ... ≤ ⌈f (g 0)⌉     : ceil_mono $ f.le_map_map_zero g

lemma lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
calc f 0 + g 0 - 1 = f 0 + (g 0 - 1) : add_sub_assoc _ _ _
               ... < f 0 + ⌊g 0⌋     : add_lt_add_left (sub_one_lt_floor _) _
               ... ≤ f (g 0)         : f.le_map_map_zero g

lemma dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 :=
begin
  rw [dist_comm, real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ← sub_eq_add_neg],
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
end

lemma dist_map_zero_lt_of_semiconj {f g₁ g₂ : circle_deg1_lift} (h : function.semiconj f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
calc dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) : dist_triangle _ _ _
... = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) :
  by simp only [h.eq, real.dist_eq, sub_sub, add_comm (f 0), sub_sub_assoc_swap, abs_sub_comm
    (g₂ (f 0))]
... < 2 : add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)

lemma dist_map_zero_lt_of_semiconj_by {f g₁ g₂ : circle_deg1_lift} (h : semiconj_by f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
dist_map_zero_lt_of_semiconj $ semiconj_by_iff_semiconj.1 h

/-!
### Limits at infinities and continuity
-/

protected lemma tendsto_at_bot : tendsto f at_bot at_bot :=
tendsto_at_bot_mono f.map_le_of_map_zero $ tendsto_at_bot_add_const_left _ _ $
  tendsto_at_bot_mono (λ x, (ceil_lt_add_one x).le) $ tendsto_at_bot_add_const_right _ _ tendsto_id

protected lemma tendsto_at_top : tendsto f at_top at_top :=
tendsto_at_top_mono f.le_map_of_map_zero $ tendsto_at_top_add_const_left _ _ $
  tendsto_at_top_mono (λ x, (sub_one_lt_floor x).le) $
    by simpa [sub_eq_add_neg] using tendsto_at_top_add_const_right _ _ tendsto_id

lemma continuous_iff_surjective : continuous f ↔ function.surjective f :=
⟨λ h, h.surjective f.tendsto_at_top f.tendsto_at_bot, f.monotone.continuous_of_surjective⟩

lemma bdd_above_set_of_map_le (f : circle_deg1_lift) (y : ℝ) :
  bdd_above {x | f x ≤ y} :=
let ⟨z, hz⟩ := eventually_at_top.1 (f.tendsto_at_top.eventually (eventually_gt_at_top y)) in
⟨z, λ x (hxy : f x ≤ y), le_of_not_lt $ λ hzx, hxy.not_lt (hz _ hzx.le)⟩

lemma bdd_below_set_of_le_map (f : circle_deg1_lift) (y : ℝ) :
  bdd_below {x | y ≤ f x} :=
let ⟨z, hz⟩ := eventually_at_bot.1 (f.tendsto_at_bot.eventually (eventually_lt_at_bot y)) in
⟨z, λ x (hxy : y ≤ f x), le_of_not_lt $ λ hzx, hxy.not_lt (hz _ hzx.le)⟩

lemma exists_map_le (f : circle_deg1_lift) (y : ℝ) : ∃ x, f x ≤ y :=
(f.tendsto_at_bot.eventually (eventually_le_at_bot y)).exists

lemma nonempty_set_of_map_le (f : circle_deg1_lift) (y : ℝ) :
  {x | f x ≤ y}.nonempty :=
f.exists_map_le y

lemma exists_le_map (f : circle_deg1_lift) (y : ℝ) : ∃ x, y ≤ f x :=
(f.tendsto_at_top.eventually (eventually_ge_at_top y)).exists

/-!
### Pointwise order on circle maps
-/

/-- Monotone circle maps form a lattice with respect to the pointwise order -/
noncomputable instance : lattice circle_deg1_lift :=
{ sup := λ f g,
  { to_fun := λ x, max (f x) (g x),
    monotone' := f.monotone.max g.monotone,
    map_add_one' := λ x, by simp [max_add_add_right] },
  le := λ f g, ∀ x, f x ≤ g x,
  le_refl := λ f x, le_refl (f x),
  le_trans := λ f₁ f₂ f₃ h₁₂ h₂₃ x, le_trans (h₁₂ x) (h₂₃ x),
  le_antisymm := λ f₁ f₂ h₁₂ h₂₁, ext $ λ x, le_antisymm (h₁₂ x) (h₂₁ x),
  le_sup_left := λ f g x, le_max_left (f x) (g x),
  le_sup_right := λ f g x, le_max_right (f x) (g x),
  sup_le := λ f₁ f₂ f₃ h₁ h₂ x, max_le (h₁ x) (h₂ x),
  inf := λ f g,
  { to_fun := λ x, min (f x) (g x),
    monotone' := f.monotone.min g.monotone,
    map_add_one' := λ x, by simp [min_add_add_right] },
  inf_le_left := λ f g x, min_le_left (f x) (g x),
  inf_le_right := λ f g x, min_le_right (f x) (g x),
  le_inf := λ f₁ f₂ f₃ h₂ h₃ x, le_min (h₂ x) (h₃ x) }

@[simp] lemma sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) := rfl

@[simp] lemma inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) := rfl

@[simp, norm_cast] lemma coe_le_coe {f g : circle_deg1_lift} : (f : ℝ → ℝ) ≤ g ↔ f ≤ g := iff.rfl

lemma monotone_apply (x : ℝ) : monotone (λ f : circle_deg1_lift, f x) := λ f g h, h x

lemma iterate_monotone (n : ℕ) : monotone (λ f : circle_deg1_lift, f^[n]) :=
λ f g h, f.monotone.iterate_le_of_le h _

lemma iterate_mono {f g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ (g^[n]) :=
iterate_monotone n h

lemma pow_mono {f g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : f^n ≤ g^n :=
λ x, by simp only [coe_pow, iterate_mono h n x]

lemma pow_monotone (n : ℕ) : monotone (λ f : circle_deg1_lift, f^n) :=
λ f g h, pow_mono h n


/-!
### Inverse map
-/

lemma right_adjoint_aux : is_order_right_adjoint f (λ y, Sup {x | f x ≤ y}) :=
is_order_right_adjoint_cSup _ f.exists_map_le f.bdd_above_set_of_map_le

noncomputable instance : has_inv circle_deg1_lift :=
⟨λ f,
  { to_fun := λ y, Sup {x | f x ≤ y},
    monotone' := f.right_adjoint_aux.right_mono,
    map_add_one' := have function.commute f (order_iso.add_right 1), from f.map_add_one,
      this.symm_adjoint f.right_adjoint_aux }⟩

lemma inv_apply (y : ℝ) : f⁻¹ y = Sup {x | f x ≤ y} := rfl

@[simp] lemma inv_one : (1 : circle_deg1_lift)⁻¹ = 1 := ext $ λ x, cSup_Iic

lemma is_order_right_adjoint_inv : is_order_right_adjoint f ⇑f⁻¹ := f.right_adjoint_aux

lemma inv_apply_le (x y : ℝ) : f⁻¹ x ≤ y ↔ 

lemma inv_inv : f⁻¹⁻¹ ≤ f :=
λ x, cSup_le _ _

end circle_deg1_lift
