/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

The space of bounded linear maps

Define the set of bounded linear maps between normed spaces and show basic facts about it. In
particular

(*) show that bounded linear maps are a vector subspace of E → F,
(*) define the operator norm and show that it induces the structure of a normed space
    on bounded linear maps.
-/
import algebra.module
import analysis.normed_space.bounded_linear_maps ring_theory.algebra
import topology.metric_space.lipschitz

variables (k : Type*) (E : Type*) (F : Type*) (G : Type*)

variables [normed_field k] [normed_space k E] [normed_space k F] [normed_space k G]

noncomputable theory
set_option class.instance_max_depth 50

structure bounded_linear_map extends linear_map k E F :=
(bound : ∃ M > 0, ∀ x : E, ∥to_fun x∥ ≤ M * ∥x∥)

variables {k E F G}
include k

lemma exists_pos_bound_of_bound {f : E → F} (M : ℝ) (h : ∀x, ∥f x∥ ≤ M * ∥x∥) :
  ∃ N > 0, ∀x, ∥f x∥ ≤ N * ∥x∥ :=
⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), λx, calc
  ∥f x∥ ≤ M * ∥x∥ : h x
  ... ≤ max M 1 * ∥x∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) ⟩

/-- Construct a bounded linear map from is_bounded_linear_map -/
def is_bounded_linear_map.to_bounded_linear_map {f : E → F}
  (hf : is_bounded_linear_map k f) : bounded_linear_map k E F :=
{ bound := hf.bound,
  ..is_bounded_linear_map.to_linear_map f hf }

namespace bounded_linear_map

notation E ` →L[`:25 k `] ` F := bounded_linear_map k E F

/-- Coerce bounded linear maps to linear maps. -/
instance : has_coe (E →L[k] F) (E →ₗ[k] F) := ⟨to_linear_map⟩

/-- Coerce bounded linear maps to functions. -/
instance to_fun : has_coe_to_fun $ E →L[k] F := ⟨_, λ f, f.to_fun⟩

@[extensionality] theorem ext {f g : E →L[k] F} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr' 1; ext x; apply h

theorem ext_iff {f g : E →L[k] F} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rintro; rw h, ext⟩

variables (c : k) (f g : E →L[k] F) (h : F →L[k] G) (x u v : E)

/-- A bounded linear map satisfies `is_bounded_linear_map` -/
lemma is_bounded_linear_map : is_bounded_linear_map k f := {..f}


-- make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero : f (0 : E) = 0 := (to_linear_map _).map_zero
@[simp] lemma map_add  : f (u + v) = f u + f v := (to_linear_map _).map_add _ _
@[simp] lemma map_sub  : f (u - v) = f u - f v := (to_linear_map _).map_sub _ _
@[simp] lemma map_smul : f (c • u) = c • f u := (to_linear_map _).map_smul _ _
@[simp] lemma map_neg  : f (-u) = - (f u) := (to_linear_map _).map_neg _

/-- The bounded map that is constantly zero. -/
def zero : E →L[k] F :=
⟨0, 1, zero_lt_one, λ x, by { change ∥(0 : F)∥ ≤ 1 * ∥x∥, simp [norm_nonneg] }⟩

instance : has_zero (E →L[k] F) := ⟨zero⟩

@[simp] lemma zero_apply : (0 : E →L[k] F) u = 0 := rfl

/-- the identity map as a bounded linear map. -/
def id : E →L[k] E :=
⟨linear_map.id, 1, zero_lt_one, λ x, le_of_eq (one_mul _).symm⟩

instance : has_one (E →L[k] E) := ⟨id⟩

@[simp] lemma id_apply : (id : E →L[k] E) u = u := rfl

instance : has_add (E →L[k] F) :=
⟨λ f g, ⟨f + g,
  let ⟨Mg, Mgpos, hMg⟩ := g.bound in
  let ⟨Mf, Mfpos, hMf⟩ := f.bound in ⟨Mf + Mg, add_pos Mfpos Mgpos, λ x,
  calc _ ≤ ∥f x∥ + ∥g x∥       : norm_triangle _ _
...      ≤ Mf * ∥x∥ + Mg * ∥x∥ : add_le_add (hMf _) (hMg _)
...      = (Mf + Mg) * ∥x∥     : (add_mul _ _ _).symm ⟩⟩⟩

@[simp] lemma add_apply : (f + g) u = f u + g u := rfl

instance : has_scalar k (E →L[k] F) :=
⟨λ c f, ⟨c • f, let ⟨M, Mpos, hM⟩ := f.bound in ⟨∥c∥ * M + 1,
  lt_of_lt_of_le (lt_add_one (0 : ℝ)) $
    add_le_add (mul_nonneg (norm_nonneg _) (le_of_lt Mpos)) (le_refl _),
  λ x, calc
  ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul _ _
  ... ≤ (∥c∥ * M + 0) * ∥x∥ :
    by { rw [add_zero, mul_assoc], exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _) }
  ... ≤ (∥c∥ * M + 1) * ∥x∥ :
    mul_le_mul_of_nonneg_right (add_le_add (le_refl _) zero_le_one) (norm_nonneg _) ⟩⟩⟩

@[simp] lemma smul_apply : (c • f) u = c • (f u) := rfl

instance : has_neg (E →L[k] F) := ⟨λ f, (-1 : k) • f⟩
instance : has_sub (E →L[k] F) := ⟨λ f g, f + (-g)⟩

@[simp] lemma neg_apply : (-f) u = - (f u) :=
by erw [smul_apply, neg_smul, one_smul]

@[simp] lemma sub_apply : (f - g) u = f u - g u :=
by { dunfold has_sub.sub, simp }

instance : add_comm_group (E →L[k] F) :=
{ add       := (+),
  add_assoc := λ _ _ _, ext $ λ _, add_assoc _ _ _,
  add_comm  := λ _ _, ext $ λ _, add_comm _ _,
  zero      := 0,
  add_zero  := λ _, ext $ λ _, add_zero _,
  zero_add  := λ _, ext $ λ _, zero_add _,
  neg       := λ f, -f,
  add_left_neg := λ f, ext $ λ x, have t: (-1 : k) • f x + f x = 0, from
    by rw neg_one_smul; exact add_left_neg _, t }

instance : vector_space k (E →L[k] F) :=
{ smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _ }

/-- Composition of bounded linear maps. -/
def comp (g : F →L[k] G) (f : E →L[k] F) : E →L[k] G :=
⟨linear_map.comp g.to_linear_map f.to_linear_map,
  let ⟨Mg, Mgpos, hMgb⟩ := g.bound in
  let ⟨Mf, Mfpos, hMfb⟩ := f.bound in ⟨Mg * Mf, mul_pos Mgpos Mfpos,
    λ x, by rw mul_assoc;
  exact le_trans (hMgb _) ((mul_le_mul_left Mgpos).2 (hMfb _))⟩⟩

instance : has_mul (bounded_linear_map k E E) := ⟨comp⟩

instance : ring (E →L[k] E) :=
{ mul := (*),
  one := 1,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl,
  left_distrib := λ _ _ _, ext $ λ _, map_add _ _ _,
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,
  ..bounded_linear_map.add_comm_group }

instance : is_ring_hom (λ c : k, c • (1 : E →L[k] E)) :=
{ map_one := one_smul _ _,
  map_add := λ _ _, ext $ λ _, add_smul _ _ _,
  map_mul := λ _ _, ext $ λ _, mul_smul _ _ _ }

instance : algebra k (E →L[k] E) :=
{ to_fun    := λ c, c • 1,
  smul_def' := λ _ _, rfl,
  commutes' := λ _ _, ext $ λ _, map_smul _ _ _ }

section
open asymptotics filter

theorem is_O_id (l : filter E): is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := f.bound in
⟨M, hMp, mem_sets_of_superset univ_mem_sets (λ x _, hM x)⟩

theorem is_O_comp (g : F →L[k] G) (f : E → F) (l : filter E) :
  is_O (λ x', g (f x')) f l :=
((g.is_O_id ⊤).comp _).mono (map_le_iff_le_comap.mp lattice.le_top)

theorem is_O_sub (f : E →L[k] F) (l : filter E) (x : E) :
  is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
is_O_comp f _ l

end

section op_norm
open set real

/-- The operator norm of a bounded linear map is the inf of all its bounds. -/
def op_norm := Inf { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }
instance has_op_norm: has_norm (E →L[k] F) := ⟨op_norm⟩

-- So that invocations of real.Inf_le make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E →L[k] F} :
  ∃ c, c ∈ { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →L[k] F} :
  bdd_below { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: ∥f x∥ ≤ ∥f∥ * ∥x∥. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
classical.by_cases
  (λ heq : x = 0, by { rw heq, simp })
  (λ hne, have hlt : 0 < ∥x∥, from (norm_pos_iff _).2 hne,
    le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by { rw mul_comm, apply hc }))))

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
(or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by { rw mul_comm, apply le_op_norm }))
  (λ heq, by { rw [←heq, div_zero], apply op_norm_nonneg }))

/-- The image of the unit ball under a bounded linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
λ hx, begin
  rw [←(mul_one ∥f∥)],
  calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
  ...    ≤ _ : mul_le_mul_of_nonneg_left hx (op_norm_nonneg _)
end

/-- If one controls the norm of every A x, then one controls the norm of A. -/
lemma bound_le_op_norm {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_triangle : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    calc _ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ...    ≤ _             : add_le_add (le_op_norm _ _) (le_op_norm _ _) }⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, bounded_linear_map.ext (λ x, (norm_le_zero_iff _).1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

/-- The operator norm is homogeneous. -/
lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
le_antisymm
  (Inf_le _ bounds_bdd_below
    ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _), λ _,
    begin
      erw [norm_smul, mul_assoc],
      exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
    end⟩)
  (lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
    (or.elim (lt_or_eq_of_le (norm_nonneg c))
      (λ hlt,
        begin
          rw mul_comm,
          exact mul_le_of_le_div hlt (Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
          (by { rw div_mul_eq_mul_div, exact le_div_of_mul_le hlt
          (by { rw [ mul_comm, ←norm_smul ], exact hc _ }) })⟩)
        end)
      (λ heq, by { rw [←heq, zero_mul], exact hn }))))

/-- Bounded linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_space : normed_space k (E →L[k] F) :=
normed_space.of_core _ _
  ⟨op_norm_zero_iff, op_norm_smul, op_norm_triangle⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le : ∥comp h f∥ ≤ ∥h∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
  begin
    rw mul_assoc,
    calc _ ≤ ∥h∥ * ∥f x∥: le_op_norm _ _
    ... ≤ _ : mul_le_mul_of_nonneg_left
              (le_op_norm _ _) (op_norm_nonneg _)
  end⟩)

/-- Bounded linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ∥f∥ f :=
⟨op_norm_nonneg _, λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }⟩

/-- Bounded linear maps are continuous. -/
theorem continuous : continuous f :=
f.lipschitz.to_continuous

end op_norm

end bounded_linear_map
