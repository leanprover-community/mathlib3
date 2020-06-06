import analysis.specific_limits
import dynamics.fixed_points
import order.iterate
import algebra.iterate_hom

open filter set
open_locale topological_space classical

-- TODO: move to a new `algebra.conj`
def {u} units.conj_hom (M : Type u) [monoid M] : units M →* mul_aut M :=
{ to_fun := λ u,
  { to_fun := λ x, ↑u * x * ↑(u⁻¹),
    inv_fun := λ x, ↑(u⁻¹) * x * u,
    left_inv := λ x, by simp  [mul_assoc],
    right_inv := λ x, by simp [mul_assoc],
    map_mul' := λ x y, by simp [mul_assoc] },
  map_one' := by { ext, simp },
  map_mul' := λ u₁ u₂, by { ext x, simp [mul_assoc] } }

-- TODO: add `mul_equiv.map_pow` to `group_power`
-- TODO: move to `group_power`
@[simp] lemma units.conj_pow {M : Type*} [monoid M] (u : units M) (x : M) (n : ℕ) :
  (u * x * ↑(u⁻¹) : M)^n = u * x^n * ↑(u⁻¹) :=
((units.conj_hom M u).to_monoid_hom.map_pow x n).symm

-- TODO: move to `group_power`
@[simp] lemma units.conj_pow' {M : Type*} [monoid M] (u : units M) (x : M) (n : ℕ) :
  (↑(u⁻¹) * x * u : M)^n = ↑(u⁻¹) * x^n * u :=
(u⁻¹).conj_pow x n

/-!
### Definition and monoid structure
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

@[mono] lemma mono {x y} (h : x ≤ y) : f x ≤ f y := f.monotone h

@[simp] lemma map_add_one : ∀ x, f (x + 1) = f x + 1 := f.map_add_one'

@[simp] lemma map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm]

theorem coe_inj : ∀ ⦃f g : circle_deg1_lift ⦄, (f : ℝ → ℝ) = g → f = g :=
assume ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h, by congr; exact h

@[ext] theorem ext ⦃f g : circle_deg1_lift ⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj $ funext h

theorem ext_iff {f g : circle_deg1_lift} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : monoid circle_deg1_lift :=
{ mul := λ f g,
  { to_fun := f ∘ g,
    monotone' := f.monotone.comp g.monotone,
    map_add_one' := λ x, by simp [map_add_one] },
  one := ⟨id, monotone_id, λ _, rfl⟩,
  mul_one := λ f, coe_inj $ function.comp.right_id f,
  one_mul := λ f, coe_inj $ function.comp.left_id f,
  mul_assoc := λ f₁ f₂ f₃, coe_inj rfl }

@[simp] lemma coe_mul : ⇑(f * g) = f ∘ g := rfl

lemma mul_apply (x) : (f * g) x = f (g x) := rfl

@[simp] lemma coe_one : ⇑(1 : circle_deg1_lift) = id := rfl

instance units_has_coe_to_fun : has_coe_to_fun (units circle_deg1_lift) :=
⟨λ _, ℝ → ℝ, λ f, ⇑(f : circle_deg1_lift)⟩

@[simp, norm_cast] lemma units_coe (f : units circle_deg1_lift) : ⇑(f : circle_deg1_lift) = f := rfl

lemma coe_pow : ∀ n : ℕ, ⇑(f^n) = (f^[n])
| 0 := rfl
| (n+1) := by {ext x, simp [coe_pow n, pow_succ'] }

lemma semiconj_by_iff_semiconj {f g₁ g₂ : circle_deg1_lift} :
  semiconj_by f g₁ g₂ ↔ function.semiconj f g₁ g₂ :=
ext_iff

lemma commute_iff_commute {f g : circle_deg1_lift} :
  commute f g ↔ function.commute f g :=
ext_iff

/-!
### Translate by a constant
-/

def translate : multiplicative ℝ →* units circle_deg1_lift :=
by refine (units.map _).comp (to_units $ multiplicative ℝ).to_monoid_hom; exact
{ to_fun := λ x, ⟨λ y, x.to_add + y, λ y₁ y₂ h, add_le_add_left h _, λ y, (add_assoc _ _ _).symm⟩,
  map_one' := ext $ zero_add,
  map_mul' := λ x y, ext $ add_assoc _ _ }

@[simp] lemma translate_apply (x y : ℝ) : translate (multiplicative.of_add x) y = x + y := rfl

@[simp]
lemma translate_inv_apply (x y : ℝ) : (translate $ multiplicative.of_add x)⁻¹ y = -x + y := rfl

@[simp] lemma translate_gpow (x : ℝ) (n : ℤ) :
  (translate (multiplicative.of_add x))^n = translate (multiplicative.of_add $ n * x) :=
by simp only [← gsmul_eq_mul, of_add_gsmul, monoid_hom.map_gpow]

@[simp] lemma translate_pow (x : ℝ) (n : ℕ) :
  (translate (multiplicative.of_add x))^n = translate (multiplicative.of_add $ n * x) :=
translate_gpow x n

@[simp] lemma translate_iterate (x : ℝ) (n : ℕ) :
  (translate (multiplicative.of_add x))^[n] = translate (multiplicative.of_add $ n * x) :=
by rw [← units_coe, ← coe_pow, ← units.coe_pow, translate_pow, units_coe]

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translation by an integer number. First we formulate
these statements (for a natural or an integer number, addition on the left or on the right, addition
or subtraction) using `function.commute`, then reformulate as `simp` lemmas `map_int_add` etc.
-/

lemma commute_nat_add (n : ℕ) : function.commute f ((+) n) :=
by simpa only [nsmul_one, add_left_iterate] using function.commute.iterate_right f.map_one_add n

lemma commute_add_nat (n : ℕ) : function.commute f (λ x, x + n) :=
by simp only [add_comm _ (n:ℝ), f.commute_nat_add n]

lemma commute_sub_nat (n : ℕ) : function.commute f (λ x, x - n) :=
(f.commute_add_nat n).inverses_right (equiv.add_right _).right_inv (equiv.add_right _).left_inv

lemma commute_add_int : ∀ n : ℤ, function.commute f (λ x, x + n)
| (n:ℕ) := f.commute_add_nat n
| -[1+n] := f.commute_sub_nat (n + 1)

lemma commute_int_add (n : ℤ) : function.commute f ((+) n) :=
by simpa only [add_comm _ (n:ℝ)] using f.commute_add_int n

lemma commute_sub_int (n : ℤ) : function.commute f (λ x, x - n) :=
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

lemma map_int_of_map_zero (n : ℤ) : f n = f 0 + n :=
by rw [← f.map_add_int, zero_add]

@[simp] lemma map_fract_sub_fract_eq (x : ℝ) :
  f (fract x) - fract x = f x - x :=
by conv_rhs { rw [← fract_add_floor x, f.map_add_int, add_sub_comm, sub_self, add_zero] }

/-!
### Pointwise order on circle maps
-/

/-- Circle maps form a lattice with respect to the pointwise -/
noncomputable instance : lattice circle_deg1_lift :=
{ sup := λ f g,
  { to_fun := λ x, max (f x) (g x),
    monotone' := λ x y h, max_le_max (f.mono h) (g.mono h), -- TODO: generalize to `monotone.max`
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
    monotone' := λ x y h, min_le_min (f.mono h) (g.mono h),
    map_add_one' := λ x, by simp [min_add_add_right] },
  inf_le_left := λ f g x, min_le_left (f x) (g x),
  inf_le_right := λ f g x, min_le_right (f x) (g x),
  le_inf := λ f₁ f₂ f₃ h₂ h₃ x, le_min (h₂ x) (h₃ x) }

@[simp] lemma sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) := rfl

@[simp] lemma inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) := rfl

lemma iterate_monotone (n : ℕ) : monotone (λ f : circle_deg1_lift, f^[n]) :=
λ f g h, f.monotone.iterate_le_of_le h _

lemma iterate_mono {f g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ (g^[n]) :=
iterate_monotone n h

lemma pow_mono {f g : circle_deg1_lift} (h : f ≤ g) (n : ℕ) : f^n ≤ g^n :=
λ x, by simp only [coe_pow, iterate_mono h n x]

lemma pow_monotone (n : ℕ) : monotone (λ f : circle_deg1_lift, f^n) :=
λ f g h, pow_mono h n

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps 
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
calc f 0 + g 0 - 1 = f 0 + (g 0 - 1) : add_assoc _ _ _
               ... < f 0 + ⌊g 0⌋     : add_lt_add_left (sub_one_lt_floor _) _
               ... ≤ f (g 0)         : f.le_map_map_zero g

lemma dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 :=
begin
  rw [dist_comm, real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add'],
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
end

lemma dist_map_zero_lt_of_semiconj {f g₁ g₂ : circle_deg1_lift} (h : function.semiconj f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
calc dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) : dist_triangle _ _ _
... = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) :
  by simp only [h.eq, real.dist_eq, sub_sub, add_comm (f 0), sub_sub_assoc_swap, abs_sub (g₂ (f 0))]
... < 2 : add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)

lemma dist_map_zero_lt_of_semiconj_by {f g₁ g₂ : circle_deg1_lift} (h : semiconj_by f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
dist_map_zero_lt_of_semiconj $ semiconj_by_iff_semiconj.1 h

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/

lemma iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) (n : ℕ) :
  f^[n] x ≤ x + n * m :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const m) h n

lemma le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : x + m ≤ f x) (n : ℕ) :
  x + n * m ≤ (f^[n]) x :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const m) f.monotone h n

lemma iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
  f^[n] x = x + n * m :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).iterate_eq_of_map_eq n h

lemma iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
  f^[n] x ≤ x + n * m ↔ f x ≤ x + m :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strict_mono_id.add_const m) hn

lemma iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
  f^[n] x < x + n * m ↔ f x < x + m :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strict_mono_id.add_const m) hn

lemma iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
  f^[n] x = x + n * m ↔ f x = x + m :=
by simpa only [nsmul_eq_mul, add_right_iterate]
using (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strict_mono_id.add_const m) hn

lemma le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
  x + n * m ≤ (f^[n]) x ↔ x + m ≤ f x :=
by simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)

lemma lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
  x + n * m < (f^[n]) x ↔ x + m < f x :=
by simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)

lemma mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊(f^[n] 0)⌋ :=
begin
  rw [le_floor, int.cast_mul, int.cast_coe_nat, ← zero_add ((n : ℝ) * _)],
  apply le_iterate_of_add_int_le_map,
  simp [floor_le]
end

/-!
### Definition of translation number
-/
noncomputable theory

def rotnum_aux_seq (n : ℕ) : ℝ := (f^(2^n)) 0 / 2^n

def translation_number : ℝ :=
lim ((at_top : filter ℕ).map f.rotnum_aux_seq)

lemma rotnum_aux_seq_def : f.rotnum_aux_seq = λ n : ℕ, (f^(2^n)) 0 / 2^n := rfl

lemma translation_number_eq_of_tendsto_aux {τ : ℝ}
  (h : tendsto f.rotnum_aux_seq at_top (𝓝 τ)) :
  translation_number f = τ :=
lim_eq (map_ne_bot at_top_ne_bot) h

lemma translation_number_eq_of_tendsto₀ {τ : ℝ}
  (h : tendsto (λ n:ℕ, f^[n] 0 / n) at_top (𝓝 τ)) :
  translation_number f = τ :=
f.translation_number_eq_of_tendsto_aux $
by simpa [(∘), rotnum_aux_seq_def, coe_pow]
using h.comp (nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two)

lemma translation_number_eq_of_tendsto₀' {τ : ℝ}
  (h : tendsto (λ n:ℕ, f^[n + 1] 0 / (n + 1)) at_top (𝓝 τ)) :
  translation_number f = τ :=
f.translation_number_eq_of_tendsto₀ $ (tendsto_add_at_top_iff_nat 1).1 h

lemma rotnum_aux_seq_zero : f.rotnum_aux_seq 0 = f 0 := by simp [rotnum_aux_seq]

lemma rotnum_aux_seq_dist_lt (n : ℕ) :
  dist (f.rotnum_aux_seq n) (f.rotnum_aux_seq (n+1)) < (1 / 2) / (2^n) :=
begin
  have : 0 < (2^(n+1):ℝ) := pow_pos zero_lt_two _,
  rw [div_div_eq_div_mul, ← pow_succ, ← abs_of_pos this],
  replace := abs_pos_iff.2 (ne_of_gt this),
  convert (div_lt_div_right this).2 ((f^(2^n)).dist_map_map_zero_lt (f^(2^n))),
  simp_rw [rotnum_aux_seq, real.dist_eq],
  rw [← abs_div, sub_div, pow_succ, ← two_mul, mul_div_mul_left _ _ (@two_ne_zero ℝ _),
    nat.pow_succ, pow_mul, pow_two, mul_apply]
end

lemma tendsto_translation_number_aux :
  tendsto f.rotnum_aux_seq at_top (𝓝 f.translation_number) :=
le_nhds_lim_of_cauchy $ cauchy_seq_of_le_geometric_two 1
  (λ n, le_of_lt $ f.rotnum_aux_seq_dist_lt n)

lemma dist_map_zero_translation_number_le :
  dist (f 0) f.translation_number ≤ 1 :=
f.rotnum_aux_seq_zero ▸ dist_le_of_le_geometric_two_of_tendsto₀ 1
  (λ n, le_of_lt $ f.rotnum_aux_seq_dist_lt n) f.tendsto_translation_number_aux

lemma tendsto_translation_number_of_dist_bounded_aux (x : ℕ → ℝ) (C : ℝ)
  (H : ∀ n : ℕ, dist ((f^n) 0) (x n) ≤ C) :
  tendsto (λ n : ℕ, x (2^n) / (2^n)) at_top (𝓝 f.translation_number) :=
begin
  refine f.tendsto_translation_number_aux.congr_dist (squeeze_zero (λ _, dist_nonneg) _ _),
  { exact λ n, C / 2^n },
  { intro n,
    have : 0 < (2^n:ℝ) := pow_pos zero_lt_two _,
    convert (div_le_div_right this).2 (H (2^n)),
    rw [rotnum_aux_seq, real.dist_eq, ← sub_div, abs_div, abs_of_pos this, real.dist_eq] },
  { exact mul_zero C ▸ tendsto_const_nhds.mul (tendsto_inv_at_top_zero.comp $
      tendsto_pow_at_top_at_top_of_one_lt one_lt_two) }
end

lemma translation_number_eq_of_dist_bounded {f g : circle_deg1_lift} (C : ℝ)
  (H : ∀ n : ℕ, dist ((f^n) 0) ((g^n) 0) ≤ C) :
  f.translation_number = g.translation_number :=
eq.symm $ g.translation_number_eq_of_tendsto_aux $
  f.tendsto_translation_number_of_dist_bounded_aux _ C H

@[simp] lemma translation_number_map_id : translation_number 1 = 0 :=
translation_number_eq_of_tendsto₀ _ $ by simp [tendsto_const_nhds]

lemma translation_number_eq_of_semiconj_by {f g₁ g₂ : circle_deg1_lift} (H : semiconj_by f g₁ g₂) :
  g₁.translation_number = g₂.translation_number :=
translation_number_eq_of_dist_bounded 2 $ λ n, le_of_lt $
  dist_map_zero_lt_of_semiconj_by $ H.pow_right n

lemma translation_number_eq_of_semiconj {f g₁ g₂ : circle_deg1_lift}
  (H : function.semiconj f g₁ g₂) :
  g₁.translation_number = g₂.translation_number :=
translation_number_eq_of_semiconj_by $ semiconj_by_iff_semiconj.2 H

lemma translation_number_mul_of_commute {f g : circle_deg1_lift} (h : commute f g) :
  (f * g).translation_number = f.translation_number + g.translation_number :=
begin
  have : tendsto (λ n : ℕ, ((λ k, (f^k) 0 + (g^k) 0) (2^n)) / (2^n)) at_top
    (𝓝 $ f.translation_number + g.translation_number) :=
    ((f.tendsto_translation_number_aux.add g.tendsto_translation_number_aux).congr $
      λ n, (add_div ((f^(2^n)) 0) ((g^(2^n)) 0) ((2:ℝ)^n)).symm),
  refine tendsto_nhds_unique at_top_ne_bot
    ((f * g).tendsto_translation_number_of_dist_bounded_aux _ 1 (λ n, _))
    this,
  rw [h.mul_pow, dist_comm],
  exact le_of_lt ((f^n).dist_map_map_zero_lt (g^n))
end

@[simp] lemma translation_number_pow :
  ∀ n : ℕ, (f^n).translation_number = n * f.translation_number
| 0 := by simp
| (n+1) := by rw [pow_succ', translation_number_mul_of_commute (commute.pow_self f n),
  translation_number_pow n, nat.cast_add_one, add_mul, one_mul]

lemma translation_number_conj_eq (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑f * g * ↑(f⁻¹)).translation_number = g.translation_number :=
(translation_number_eq_of_semiconj_by (semiconj_by.units_conj_mk _ _)).symm

lemma translation_number_conj_eq' (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑(f⁻¹) * g * f).translation_number = g.translation_number :=
translation_number_conj_eq f⁻¹ g

lemma dist_pow_map_zero_mul_translation_number_le (n:ℕ) :
  dist ((f^n) 0) (n * f.translation_number) ≤ 1 :=
f.translation_number_pow n ▸ (f^n).dist_map_zero_translation_number_le

lemma tendsto_translation_number₀' :
  tendsto (λ n:ℕ, (f^(n+1)) 0 / (n+1)) at_top (𝓝 f.translation_number) :=
begin
  refine (tendsto_iff_dist_tendsto_zero.2 $ squeeze_zero (λ _, dist_nonneg) (λ n, _)
    ((tendsto_const_div_at_top_nhds_0_nat 1).comp (tendsto_add_at_top_nat 1))),
  dsimp,
  have : (0:ℝ) < n + 1 := n.cast_add_one_pos,
  rw [real.dist_eq, div_sub' _ _ _ (ne_of_gt this), abs_div, ← real.dist_eq, abs_of_pos this,
    div_le_div_right this, ← nat.cast_add_one],
  apply dist_pow_map_zero_mul_translation_number_le
end

lemma tendsto_translation_number₀ :
  tendsto (λ n:ℕ, ((f^n) 0) / n) at_top (𝓝 f.translation_number) :=
(tendsto_add_at_top_iff_nat 1).1 f.tendsto_translation_number₀'

/-- For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
In particular, this limit does not depend on `x`. -/
lemma tendsto_translation_number (x : ℝ) :
  tendsto (λ n:ℕ, ((f^n) x - x) / n) at_top (𝓝 f.translation_number) :=
begin
  rw [← translation_number_conj_eq' (translate $ multiplicative.of_add x)],
  convert tendsto_translation_number₀ _,
  ext n,
  simp [sub_eq_neg_add]
end

lemma tendsto_translation_number' (x : ℝ) :
  tendsto (λ n:ℕ, ((f^(n+1)) x - x) / (n+1)) at_top (𝓝 f.translation_number) :=
(tendsto_add_at_top_iff_nat 1).2 (f.tendsto_translation_number x)

lemma translation_number_mono : monotone translation_number :=
λ f g h, le_of_tendsto_of_tendsto' at_top_ne_bot f.tendsto_translation_number₀
  g.tendsto_translation_number₀ $ λ n, div_le_div_of_le_of_nonneg (pow_mono h n 0) n.cast_nonneg

lemma translation_number_translate (x : ℝ) :
  translation_number (translate $ multiplicative.of_add x) = x :=
translation_number_eq_of_tendsto₀' _ $
  by simp [nat.cast_add_one_ne_zero, mul_div_cancel_left, tendsto_const_nhds]

lemma translation_number_le_of_le_add {z : ℝ} (hz : ∀ x, f x ≤ x + z) :
  translation_number f ≤ z :=
translation_number_translate z ▸ translation_number_mono
  (λ x, trans_rel_left _ (hz x) (add_comm _ _))

lemma le_translation_number_of_add_le {z : ℝ} (hz : ∀ x, x + z ≤ f x) :
  z ≤ translation_number f :=
translation_number_translate z ▸ translation_number_mono
  (λ x, trans_rel_right _ (add_comm _ _) (hz x))

lemma translation_number_le_of_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) :
  translation_number f ≤ m :=
le_of_tendsto' at_top_ne_bot (f.tendsto_translation_number' x) $ λ n,
div_le_of_le_mul n.cast_add_one_pos $ sub_le_iff_le_add'.2 $
(coe_pow f (n + 1)).symm ▸ f.iterate_le_of_map_le_add_int h (n + 1)

lemma translation_number_le_of_le_add_nat {x : ℝ} {m : ℕ} (h : f x ≤ x + m) :
  translation_number f ≤ m :=
@translation_number_le_of_le_add_int f x m h

lemma le_translation_number_of_add_int_le {x : ℝ} {m : ℤ} (h : x + m ≤ f x) :
  ↑m ≤ translation_number f :=
ge_of_tendsto' at_top_ne_bot (f.tendsto_translation_number' x) $ λ n,
le_div_of_mul_le n.cast_add_one_pos $ le_sub_iff_add_le'.2 $
by simp only [coe_pow, mul_comm (m:ℝ), ← nat.cast_add_one, f.le_iterate_of_add_int_le_map h]

lemma le_translation_number_of_add_nat_le {x : ℝ} {m : ℕ} (h : x + m ≤ f x) :
  ↑m ≤ translation_number f :=
@le_translation_number_of_add_int_le f x m h

/-- If `f x - x` is an integer number `m` for some point `x`, then `translation_number f = m`.
On the circle this means that a map with a fixed point has rotation number zero. -/
lemma translation_number_of_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) :
  f.translation_number = m :=
le_antisymm (translation_number_le_of_le_add_int f $ le_of_eq h)
  (le_translation_number_of_add_int_le f $ le_of_eq h.symm)

lemma floor_sub_le_translation_number (x : ℝ) : ↑⌊f x - x⌋ ≤ translation_number f :=
le_translation_number_of_add_int_le f $ le_sub_iff_add_le'.1 (floor_le $ f x - x)

lemma translation_number_le_ceil_sub (x : ℝ) : translation_number f ≤ ⌈f x - x⌉ :=
translation_number_le_of_le_add_int f $ sub_le_iff_le_add'.1 (le_ceil $ f x - x)

lemma map_lt_of_translation_number_lt_int {n : ℤ} (h : translation_number f < n) (x : ℝ) :
  f x < x + n :=
not_le.1 $ mt f.le_translation_number_of_add_int_le $ not_le.2 h

lemma map_lt_of_translation_number_lt_nat {n : ℕ} (h : translation_number f < n) (x : ℝ) :
  f x < x + n :=
@map_lt_of_translation_number_lt_int f n h x

lemma lt_map_of_int_lt_translation_number {n : ℤ} (h : ↑n < translation_number f) (x : ℝ) :
  x + n < f x :=
not_le.1 $ mt f.translation_number_le_of_le_add_int $ not_le.2 h

lemma lt_map_of_nat_lt_translation_number {n : ℕ} (h : ↑n < translation_number f) (x : ℝ) :
  x + n < f x :=
@lt_map_of_int_lt_translation_number f n h x

/-- If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`translation_number f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number. -/
lemma translation_number_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ}
  (h : (f^n) x = x + m) (hn : 0 < n) :
  f.translation_number = m / n :=
begin
  have := (f^n).translation_number_of_eq_add_int h,
  rwa [translation_number_pow, mul_comm, ← eq_div_iff] at this,
  exact nat.cast_ne_zero.2 (ne_of_gt hn)
end

lemma forall_map_sub_of_Icc (P : ℝ → Prop)
  (h : ∀ x ∈ Icc (0:ℝ) 1, P (f x - x)) (x : ℝ) : P (f x - x) :=
f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩

lemma translation_number_lt_of_forall_lt_add (hf : continuous f) {z : ℝ}
  (hz : ∀ x, f x < x + z) : f.translation_number < z :=
begin
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f y - y ≤ f x - x,
    from compact_Icc.exists_forall_ge (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuous_on,
  refine lt_of_le_of_lt _ (sub_lt_iff_lt_add'.2 $ hz x),
  apply translation_number_le_of_le_add,
  simp only [← sub_le_iff_le_add'],
  exact f.forall_map_sub_of_Icc (λ a, a ≤ f x - x) hx
end

lemma lt_translation_number_of_forall_add_lt (hf : continuous f) {z : ℝ}
  (hz : ∀ x, x + z < f x) : z < f.translation_number :=
begin
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f x - x ≤ f y - y,
    from compact_Icc.exists_forall_le (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuous_on,
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 $ hz x) _,
  apply le_translation_number_of_add_le,
  simp only [← le_sub_iff_add_le'],
  exact f.forall_map_sub_of_Icc _ hx
end

/-- If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
such that `f x = x + translation_number f`. -/
lemma exists_eq_add_translation_number (hf : continuous f) :
  ∃ x, f x = x + translation_number f :=
begin
  obtain ⟨a, ha⟩ : ∃ x, f x ≤ x + f.translation_number,
  { by_contradiction H,
    push_neg at H,
    exact lt_irrefl _ (f.lt_translation_number_of_forall_add_lt hf H) },
  obtain ⟨b, hb⟩ : ∃ x, x + f.translation_number ≤ f x,
  { by_contradiction H,
    push_neg at H,
    exact lt_irrefl _ (f.translation_number_lt_of_forall_lt_add hf H) },
  exact intermediate_value_univ₂ hf (continuous_id.add continuous_const) ha hb
end

lemma translation_number_eq_int_iff (hf : continuous f) {m : ℤ} :
  f.translation_number = m ↔ ∃ x, f x = x + m :=
begin
  refine ⟨λ h, h ▸ f.exists_eq_add_translation_number hf, _⟩,
  rintros ⟨x, hx⟩,
  exact f.translation_number_of_eq_add_int hx
end

lemma continuous_pow (hf : continuous f) (n : ℕ) :
  continuous ⇑(f^n : circle_deg1_lift) :=
by { rw coe_pow, exact hf.iterate n }

lemma translation_number_eq_rat_iff (hf : continuous f) {m : ℤ}
  {n : ℕ} (hn : 0 < n) :
  f.translation_number = m / n ↔ ∃ x, (f^n) x = x + m :=
begin
  rw [eq_div_iff, mul_comm, ← translation_number_pow]; [skip, exact ne_of_gt (nat.cast_pos.2 hn)],
  exact (f^n).translation_number_eq_int_iff (f.continuous_pow hf n)
end

end circle_deg1_lift
