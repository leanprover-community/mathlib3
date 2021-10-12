/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.unit_interval
import topology.algebra.ordered.proj_Icc
import topology.continuous_function.basic

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `path.map` is the image of a path under a continuous map.
* `joined (x y : X)` means there is a path between `x` and `y`.
* `joined.some_path (h : joined x y)` selects some path between two points `x` and `y`.
* `path_component (x : X)` is the set of points joined to `x`.
* `path_connected_space X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : set X`.

* `joined_in F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `joined_in.some_path (h : joined_in F x y)` selects a path from `x` to `y` inside `F`.
* `path_component_in F (x : X)` is the set of points joined to `x` in `F`.
* `is_path_connected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `loc_path_connected_space X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `joined` and `joined_in F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : set X)` or the
subtype `↥F`.

* `path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X)`
* `is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space ↥F`

For locally path connected spaces, we have
* `path_connected_space_iff_connected_space : path_connected_space X ↔ connected_space X`
* `is_connected_iff_is_path_connected (U_op : is_open U) : is_path_connected U ↔ is_connected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `set.Icc_extend` that will extend any continuous map `γ : I → X` into a continuous map
`Icc_extend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `path.extend` that turns `γ : path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

noncomputable theory
open_locale classical topological_space filter unit_interval
open filter set function unit_interval

variables {X : Type*} [topological_space X] {x y z : X} {ι : Type*}

/-! ### Paths -/

/-- Continuous path connecting two points `x` and `y` in a topological space -/
@[nolint has_inhabited_instance]
structure path (x y : X) extends C(I, X) :=
(source' : to_fun 0 = x)
(target' : to_fun 1 = y)

instance : has_coe_to_fun (path x y) := ⟨_, λ p, p.to_fun⟩

@[ext] protected lemma path.ext {X : Type*} [topological_space X] {x y : X} :
  ∀ {γ₁ γ₂ : path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂
| ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨.(x), h21⟩, h22, h23⟩ rfl := rfl

namespace path

@[simp] lemma coe_mk (f : I → X) (h₁ h₂ h₃) : ⇑(mk ⟨f, h₁⟩ h₂ h₃ : path x y) = f := rfl

variable (γ : path x y)

@[continuity]
protected lemma continuous : continuous γ :=
γ.continuous_to_fun

@[simp] protected lemma source : γ 0 = x :=
γ.source'

@[simp] protected lemma target : γ 1 = y :=
γ.target'

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X := γ

initialize_simps_projections path (to_continuous_map_to_fun → simps.apply, -to_continuous_map)

@[simp] lemma coe_to_continuous_map : ⇑γ.to_continuous_map = γ := rfl

/-- Any function `φ : Π (a : α), path (x a) (y a)` can be seen as a function `α × I → X`. -/
instance has_uncurry_path {X α : Type*} [topological_space X] {x y : α → X} :
  has_uncurry (Π (a : α), path (x a) (y a)) (α × I) X :=
⟨λ φ p, φ p.1 p.2⟩

/-- The constant path from a point to itself -/
@[refl, simps] def refl (x : X) : path x x :=
{ to_fun := λ t, x,
  continuous_to_fun := continuous_const,
  source' := rfl,
  target' := rfl }

@[simp] lemma refl_range {X : Type*} [topological_space X] {a : X} :
  range (path.refl a) = {a} :=
by simp [path.refl, has_coe_to_fun.coe, coe_fn]

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps] def symm (γ : path x y) : path y x :=
{ to_fun      := γ ∘ σ,
  continuous_to_fun := by continuity,
  source'       := by simpa [-path.target] using γ.target,
  target'      := by simpa [-path.source] using γ.source }

@[simp] lemma refl_symm {X : Type*} [topological_space X] {a : X} :
  (path.refl a).symm = path.refl a :=
by { ext, refl }

@[simp] lemma symm_range {X : Type*} [topological_space X] {a b : X} (γ : path a b) :
  range γ.symm = range γ :=
begin
  ext x,
  simp only [mem_range, path.symm, has_coe_to_fun.coe, coe_fn, unit_interval.symm, set_coe.exists,
    comp_app, subtype.coe_mk, subtype.val_eq_coe],
  split; rintros ⟨y, hy, hxy⟩; refine ⟨1-y, mem_iff_one_sub_mem.mp hy, _⟩; convert hxy,
  simp
end

/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : ℝ → X := Icc_extend zero_le_one γ

@[continuity]
lemma continuous_extend : continuous γ.extend :=
γ.continuous.Icc_extend

@[simp] lemma extend_extends {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ∈ (Icc 0 1 : set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
Icc_extend_of_mem _ γ ht

lemma extend_zero : γ.extend 0 = x :=
by simp

lemma extend_one : γ.extend 1 = y :=
by simp

@[simp] lemma extend_extends' {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : (Icc 0 1 : set ℝ)) : γ.extend t = γ t :=
Icc_extend_coe _ γ t

@[simp] lemma extend_range {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : range γ.extend = range γ :=
Icc_extend_range _ γ

lemma extend_of_le_zero {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : t ≤ 0) : γ.extend t = a :=
(Icc_extend_of_le_left _ _ ht).trans γ.source

lemma extend_of_one_le {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t : ℝ} (ht : 1 ≤ t) : γ.extend t = b :=
(Icc_extend_of_right_le _ _ ht).trans γ.target

@[simp] lemma refl_extend {X : Type*} [topological_space X] {a : X} :
  (path.refl a).extend = λ _, a := rfl

/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def of_line {f : ℝ → X} (hf : continuous_on f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : path x y :=
{ to_fun := f ∘ coe,
  continuous_to_fun := hf.comp_continuous continuous_subtype_coe subtype.prop,
  source' := h₀,
  target' := h₁ }

lemma of_line_mem {f : ℝ → X} (hf : continuous_on f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
  ∀ t, of_line hf h₀ h₁ t ∈ f '' I :=
λ ⟨t, t_in⟩, ⟨t, t_in, rfl⟩

local attribute [simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans] def trans (γ : path x y) (γ' : path y z) : path x z :=
{ to_fun := (λ t : ℝ, if t ≤ 1/2 then γ.extend (2*t) else γ'.extend (2*t-1)) ∘ coe,
  continuous_to_fun :=
  begin
    refine (continuous.if_le _ _ continuous_id continuous_const (by norm_num)).comp
      continuous_subtype_coe,
    -- TODO: the following are provable by `continuity` but it is too slow
    exacts [γ.continuous_extend.comp (continuous_const.mul continuous_id),
      γ'.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)]
  end,
  source' := by norm_num,
  target' := by norm_num }

@[simp] lemma refl_trans_refl {X : Type*} [topological_space X] {a : X} :
  (path.refl a).trans (path.refl a) = path.refl a :=
begin
  ext,
  simp only [path.trans, if_t_t, one_div, path.refl_extend],
  refl
end

lemma trans_range {X : Type*} [topological_space X] {a b c : X}
  (γ₁ : path a b) (γ₂ : path b c) : range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ :=
begin
  rw path.trans,
  apply eq_of_subset_of_subset,
  { rintros x ⟨⟨t, ht0, ht1⟩, hxt⟩,
    by_cases h : t ≤ 1/2,
    { left,
      use [2*t, ⟨by linarith, by linarith⟩],
      rw ← γ₁.extend_extends,
      unfold_coes at hxt,
      simp only [h, comp_app, if_true] at hxt,
      exact hxt },
    { right,
      use [2*t-1, ⟨by linarith, by linarith⟩],
      rw ← γ₂.extend_extends,
      unfold_coes at hxt,
      simp only [h, comp_app, if_false] at hxt,
      exact hxt } },
  { rintros x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩),
    { use ⟨t/2, ⟨by linarith, by linarith⟩⟩,
      unfold_coes,
      have : t/2 ≤ 1/2 := by linarith,
      simp only [this, comp_app, if_true],
      ring_nf,
      rwa γ₁.extend_extends },
    { by_cases h : t = 0,
      { use ⟨1/2, ⟨by linarith, by linarith⟩⟩,
        unfold_coes,
        simp only [h, comp_app, if_true, le_refl, mul_one_div_cancel (@two_ne_zero ℝ _ _)],
        rw γ₁.extend_one,
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt },
      { use ⟨(t+1)/2, ⟨by linarith, by linarith⟩⟩,
        unfold_coes,
        change t ≠ 0 at h,
        have ht0 := lt_of_le_of_ne ht0 h.symm,
        have : ¬ (t+1)/2 ≤ 1/2 := by {rw not_le, linarith},
        simp only [comp_app, if_false, this],
        ring_nf,
        rwa γ₂.extend_extends } } }
end

/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : path x y) {Y : Type*} [topological_space Y]
  {f : X → Y} (h : continuous f) : path (f x) (f y) :=
{ to_fun := f ∘ γ,
  continuous_to_fun := by continuity,
  source' := by simp,
  target' := by simp }

@[simp] lemma map_coe (γ : path x y) {Y : Type*} [topological_space Y]
  {f : X → Y} (h : continuous f) :
  (γ.map h : I → Y) = f ∘ γ :=
by { ext t, refl }

/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : path x y) {x' y'} (hx : x' = x) (hy : y' = y) : path x' y' :=
{ to_fun := γ,
  continuous_to_fun := γ.continuous,
  source' := by simp [hx],
  target' := by simp [hy] }

@[simp] lemma symm_cast {X : Type*} [topological_space X] {a₁ a₂ b₁ b₂ : X}
  (γ : path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
  (γ.cast ha hb).symm = (γ.symm).cast hb ha := rfl

@[simp] lemma trans_cast {X : Type*} [topological_space X] {a₁ a₂ b₁ b₂ c₁ c₂ : X}
  (γ : path a₂ b₂) (γ' : path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
  (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc := rfl

@[simp] lemma cast_coe (γ : path x y) {x' y'} (hx : x' = x) (hy : y' = y) :
  (γ.cast hx hy : I → X) = γ :=
rfl

@[continuity]
lemma symm_continuous_family {X ι : Type*} [topological_space X] [topological_space ι]
  {a b : ι → X} (γ : Π (t : ι), path (a t) (b t)) (h : continuous ↿γ) :
  continuous ↿(λ t, (γ t).symm) :=
h.comp (continuous_id.prod_map continuous_symm)

@[continuity]
lemma continuous_uncurry_extend_of_continuous_family {X ι : Type*} [topological_space X]
  [topological_space ι] {a b : ι → X}  (γ : Π (t : ι), path (a t) (b t)) (h : continuous ↿γ) :
  continuous ↿(λ t, (γ t).extend) :=
h.comp (continuous_id.prod_map continuous_proj_Icc)

@[continuity]
lemma trans_continuous_family {X ι : Type*} [topological_space X] [topological_space ι]
  {a b c : ι → X}
  (γ₁ : Π (t : ι), path (a t) (b t)) (h₁ : continuous ↿γ₁)
  (γ₂ : Π (t : ι), path (b t) (c t)) (h₂ : continuous ↿γ₂) :
  continuous ↿(λ t, (γ₁ t).trans (γ₂ t)) :=
begin
  have h₁' := path.continuous_uncurry_extend_of_continuous_family γ₁ h₁,
  have h₂' := path.continuous_uncurry_extend_of_continuous_family γ₂ h₂,
  simp only [has_uncurry.uncurry, has_coe_to_fun.coe, coe_fn, path.trans, (∘)],
  refine continuous.if_le _ _ (continuous_subtype_coe.comp continuous_snd) continuous_const _,
  { change continuous ((λ p : ι × ℝ, (γ₁ p.1).extend p.2) ∘ (prod.map id (λ x, 2*x : I → ℝ))),
    exact h₁'.comp (continuous_id.prod_map $ continuous_const.mul continuous_subtype_coe) },
  { change continuous ((λ p : ι × ℝ, (γ₂ p.1).extend p.2) ∘ (prod.map id (λ x, 2*x - 1 : I → ℝ))),
    exact h₂'.comp (continuous_id.prod_map $
      (continuous_const.mul continuous_subtype_coe).sub continuous_const) },
  { rintros st hst,
    simp [hst, mul_inv_cancel (@two_ne_zero ℝ _ _)] }
end

/-! #### Truncating a path -/

/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the
  time interval `[t₀, t₁]` and stays still otherwise. -/
def truncate {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t₀ t₁ : ℝ) : path (γ.extend $ min t₀ t₁) (γ.extend t₁) :=
{ to_fun := λ s, γ.extend (min (max s t₀) t₁),
  continuous_to_fun := γ.continuous_extend.comp
    ((continuous_subtype_coe.max continuous_const).min continuous_const),
  source' :=
  begin
    simp only [min_def, max_def],
    norm_cast,
    split_ifs with h₁ h₂ h₃ h₄,
    { simp [γ.extend_of_le_zero h₁] },
    { congr, linarith },
    { have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂),
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁] },
    all_goals { refl }
  end,
  target' :=
  begin
    simp only [min_def, max_def],
    norm_cast,
    split_ifs with h₁ h₂ h₃,
    { simp [γ.extend_of_one_le h₂] },
    { refl },
    { have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁),
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)] },
    { refl }
  end }

/-- `γ.truncate_of_le t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
  casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncate_of_le {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) : path (γ.extend t₀) (γ.extend t₁) :=
(γ.truncate t₀ t₁).cast (by rw min_eq_left h) rfl

lemma truncate_range {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) {t₀ t₁ : ℝ} : range (γ.truncate t₀ t₁) ⊆ range γ :=
begin
  rw ← γ.extend_range,
  simp only [range_subset_iff, set_coe.exists, set_coe.forall],
  intros x hx,
  simp only [has_coe_to_fun.coe, coe_fn, path.truncate, mem_range_self]
end

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
lemma truncate_continuous_family {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : continuous (λ x, γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
γ.continuous_extend.comp
  (((continuous_subtype_coe.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
    (continuous_fst.comp continuous_snd))
/- TODO : When `continuity` gets quicker, change the proof back to :
    `begin`
      `simp only [has_coe_to_fun.coe, coe_fn, path.truncate],`
      `continuity,`
      `exact continuous_subtype_coe`
    `end` -/

@[continuity]
lemma truncate_const_continuous_family {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : ℝ) : continuous ↿(γ.truncate t) :=
have key : continuous (λ x, (t, x) : ℝ × I → ℝ × ℝ × I) := continuous_const.prod_mk continuous_id,
by convert γ.truncate_continuous_family.comp key

@[simp] lemma truncate_self {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t : ℝ) : γ.truncate t t = (path.refl $ γ.extend t).cast (by rw min_self) rfl :=
begin
  ext x,
  rw cast_coe,
  simp only [truncate, has_coe_to_fun.coe, coe_fn, refl, min_def, max_def],
  split_ifs with h₁ h₂; congr,
  exact le_antisymm ‹_› ‹_›
end

@[simp] lemma truncate_zero_zero {X : Type*} [topological_space X] {a b : X} (γ : path a b) :
  γ.truncate 0 0 = (path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero :=
by convert γ.truncate_self 0; exact γ.extend_zero.symm

@[simp] lemma truncate_one_one {X : Type*} [topological_space X] {a b : X} (γ : path a b) :
  γ.truncate 1 1 = (path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one :=
by convert γ.truncate_self 1; exact γ.extend_one.symm

@[simp] lemma truncate_zero_one {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) : γ.truncate 0 1 = γ.cast (by simp [zero_le_one, extend_zero]) (by simp) :=
begin
  ext x,
  rw cast_coe,
  have : ↑x ∈ (Icc 0 1 : set ℝ) := x.2,
  rw [truncate, coe_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']
end

/-! #### Reparametrising a path -/

/--
Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : path x y) (f : I → I) (hfcont : continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  path x y :=
{ to_fun := γ ∘ f,
  continuous_to_fun := by continuity,
  source' := by simp [hf₀],
  target' := by simp [hf₁] }

@[simp]
lemma coe_to_fun (γ : path x y) {f : I → I} (hfcont : continuous f) (hf₀ : f 0 = 0)
  (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f := rfl

@[simp]
lemma reparam_id (γ : path x y) : γ.reparam id continuous_id rfl rfl = γ :=
by { ext, refl }

lemma range_reparam (γ : path x y) {f : I → I} (hfcont : continuous f) (hf₀ : f 0 = 0)
  (hf₁ : f 1 = 1) : range ⇑(γ.reparam f hfcont hf₀ hf₁) = range γ :=
begin
  change range (γ ∘ f) = range γ,
  have : range f = univ,
  { rw range_iff_surjective,
    intro t,
    have h₁ : continuous (Icc_extend (@zero_le_one ℝ _) f),
    { continuity },
    have := intermediate_value_Icc (@zero_le_one ℝ _) h₁.continuous_on,
    { rw [Icc_extend_left, Icc_extend_right] at this,
      change Icc (f 0) (f 1) ⊆ _ at this,
      rw [hf₀, hf₁] at this,
      rcases this t.2 with ⟨w, hw₁, hw₂⟩,
      rw Icc_extend_of_mem _ _ hw₁ at hw₂,
      use [⟨w, hw₁⟩, hw₂] } },
  rw [range_comp, this, image_univ],
end

lemma refl_reparam {f : I → I} (hfcont : continuous f) (hf₀ : f 0 = 0)
  (hf₁ : f 1 = 1) : (refl x).reparam f hfcont hf₀ hf₁ = refl x :=
begin
  ext,
  simp,
end

end path

/-! ### Being joined by a path -/

/-- The relation "being joined by a path". This is an equivalence relation. -/
def joined (x y : X) : Prop :=
nonempty (path x y)

@[refl] lemma joined.refl (x : X) : joined x x :=
⟨path.refl x⟩

/-- When two points are joined, choose some path from `x` to `y`. -/
def joined.some_path (h : joined x y) : path x y :=
nonempty.some h

@[symm] lemma joined.symm {x y : X} (h : joined x y) : joined y x :=
⟨h.some_path.symm⟩

@[trans] lemma joined.trans {x y z : X} (hxy : joined x y) (hyz : joined y z) :
  joined x z :=
⟨hxy.some_path.trans hyz.some_path⟩

variables (X)

/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def path_setoid : setoid X :=
{ r := joined,
  iseqv := mk_equivalence _ joined.refl (λ x y, joined.symm) (λ x y z, joined.trans) }

/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def zeroth_homotopy := quotient (path_setoid X)

instance : inhabited (zeroth_homotopy ℝ) := ⟨@quotient.mk ℝ (path_setoid ℝ) 0⟩

variables {X}

/-! ### Being joined by a path inside a set -/

/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def joined_in (F : set X) (x y : X) : Prop :=
∃ γ : path x y, ∀ t, γ t ∈ F

variables {F : set X}

lemma joined_in.mem (h : joined_in F x y) : x ∈ F ∧ y ∈ F :=
begin
  rcases h with ⟨γ, γ_in⟩,
  have : γ 0 ∈ F ∧ γ 1 ∈ F, by { split; apply γ_in },
  simpa using this
end

lemma joined_in.source_mem (h : joined_in F x y) : x ∈ F :=
h.mem.1

lemma joined_in.target_mem (h : joined_in F x y) : y ∈ F :=
h.mem.2

/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def joined_in.some_path (h : joined_in F x y) : path x y :=
classical.some h

lemma joined_in.some_path_mem (h : joined_in F x y) (t : I) : h.some_path t ∈ F :=
classical.some_spec h t

/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
lemma joined_in.joined_subtype (h : joined_in F x y) :
  joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
⟨{ to_fun := λ t, ⟨h.some_path t, h.some_path_mem t⟩,
   continuous_to_fun := by continuity,
   source' := by simp,
   target' := by simp }⟩

lemma joined_in.of_line {f : ℝ → X} (hf : continuous_on f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  (hF : f '' I ⊆ F) : joined_in F x y :=
⟨path.of_line hf h₀ h₁, λ t, hF $ path.of_line_mem hf h₀ h₁ t⟩

lemma joined_in.joined (h : joined_in F x y) : joined x y :=
⟨h.some_path⟩

lemma joined_in_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
  joined_in F x y ↔ joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
⟨λ h, h.joined_subtype, λ h, ⟨h.some_path.map continuous_subtype_coe, by simp⟩⟩

@[simp] lemma joined_in_univ : joined_in univ x y ↔ joined x y :=
by simp [joined_in, joined, exists_true_iff_nonempty]

lemma joined_in.mono {U V : set X} (h : joined_in U x y) (hUV : U ⊆ V) : joined_in V x y :=
⟨h.some_path, λ t, hUV (h.some_path_mem t)⟩

lemma joined_in.refl (h : x ∈ F) : joined_in F x x :=
⟨path.refl x, λ t, h⟩

@[symm] lemma joined_in.symm (h : joined_in F x y) : joined_in F y x :=
begin
  cases h.mem with hx hy,
  simp [joined_in_iff_joined, *] at *,
  exact h.symm
end

lemma joined_in.trans (hxy : joined_in F x y) (hyz : joined_in F y z) : joined_in F x z :=
begin
  cases hxy.mem with hx hy,
  cases hyz.mem with hx hy,
  simp [joined_in_iff_joined, *] at *,
  exact hxy.trans hyz
end

/-! ### Path component -/

/-- The path component of `x` is the set of points that can be joined to `x`. -/
def path_component (x : X) := {y | joined x y}

@[simp] lemma mem_path_component_self (x : X) : x ∈ path_component x :=
joined.refl x

@[simp] lemma path_component.nonempty (x : X) : (path_component x).nonempty :=
⟨x, mem_path_component_self x⟩

lemma mem_path_component_of_mem (h : x ∈ path_component y) : y ∈ path_component x :=
joined.symm h

lemma path_component_symm : x ∈ path_component y ↔ y ∈ path_component x :=
⟨λ h, mem_path_component_of_mem h, λ h, mem_path_component_of_mem h⟩

lemma path_component_congr (h : x ∈ path_component y) : path_component x = path_component y :=
begin
  ext z,
  split,
  { intro h',
    rw path_component_symm,
    exact (h.trans h').symm },
  { intro h',
    rw path_component_symm at h' ⊢,
    exact h'.trans h },
end

lemma path_component_subset_component (x : X) : path_component x ⊆ connected_component x :=
λ y h, (is_connected_range h.some_path.continuous).subset_connected_component
  ⟨0, by simp⟩ ⟨1, by simp⟩

/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def path_component_in (x : X) (F : set X) := {y | joined_in F x y}

@[simp] lemma path_component_in_univ (x : X) : path_component_in x univ = path_component x :=
by simp [path_component_in, path_component, joined_in, joined, exists_true_iff_nonempty]

lemma joined.mem_path_component (hyz : joined y z) (hxy : y ∈ path_component x) :
  z ∈ path_component x :=
hxy.trans hyz

/-! ### Path connected sets -/

/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def is_path_connected (F : set X) : Prop := ∃ x ∈ F, ∀ {y}, y ∈ F → joined_in F x y

lemma is_path_connected_iff_eq : is_path_connected F ↔ ∃ x ∈ F, path_component_in x F = F :=
begin
  split ; rintros ⟨x, x_in, h⟩ ; use [x, x_in],
  { ext y,
    exact ⟨λ hy, hy.mem.2, h⟩ },
  { intros y y_in,
    rwa ← h at y_in },
end

lemma is_path_connected.joined_in (h : is_path_connected F) : ∀ x y ∈ F, joined_in F x y :=
λ x y x_in y_in, let ⟨b, b_in, hb⟩ := h in (hb x_in).symm.trans (hb y_in)

lemma is_path_connected_iff : is_path_connected F ↔ F.nonempty ∧ ∀ x y ∈ F, joined_in F x y :=
⟨λ h, ⟨let ⟨b, b_in, hb⟩ := h in ⟨b, b_in⟩, h.joined_in⟩,
 λ ⟨⟨b, b_in⟩, h⟩, ⟨b, b_in, λ x x_in, h b x b_in x_in⟩⟩

lemma is_path_connected.image {Y : Type*} [topological_space Y] (hF : is_path_connected F)
  {f : X → Y} (hf : continuous f) : is_path_connected (f '' F) :=
begin
  rcases hF with ⟨x, x_in, hx⟩,
  use [f x, mem_image_of_mem f x_in],
  rintros _ ⟨y, y_in, rfl⟩,
  exact ⟨(hx y_in).some_path.map hf, λ t, ⟨_, (hx y_in).some_path_mem t, rfl⟩⟩,
end

lemma is_path_connected.mem_path_component (h : is_path_connected F) (x_in : x ∈ F) (y_in : y ∈ F) :
  y ∈ path_component x :=
(h.joined_in x y x_in y_in).joined

lemma is_path_connected.subset_path_component (h : is_path_connected F) (x_in : x ∈ F) :
  F ⊆ path_component x :=
λ y y_in, h.mem_path_component x_in y_in

lemma is_path_connected.union {U V : set X} (hU : is_path_connected U) (hV : is_path_connected V)
  (hUV : (U ∩ V).nonempty) : is_path_connected (U ∪ V) :=
begin
  rcases hUV with ⟨x, xU, xV⟩,
  use [x, or.inl xU],
  rintros y (yU | yV),
  { exact (hU.joined_in x y xU yU).mono (subset_union_left U V) },
  { exact (hV.joined_in x y xV yV).mono (subset_union_right U V) },
end

/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
lemma is_path_connected.preimage_coe {U W : set X} (hW : is_path_connected W) (hWU : W ⊆ U) :
  is_path_connected ((coe : U → X) ⁻¹' W) :=
begin
  rcases hW with ⟨x, x_in, hx⟩,
  use [⟨x, hWU x_in⟩, by simp [x_in]],
  rintros ⟨y, hyU⟩ hyW,
  exact ⟨(hx hyW).joined_subtype.some_path.map (continuous_inclusion hWU), by simp⟩
end

lemma is_path_connected.exists_path_through_family
  {X : Type*} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s)
  (p : fin (n+1) → X) (hp : ∀ i, p i ∈ s) :
  ∃ γ : path (p 0) (p n), (range γ ⊆ s) ∧ (∀ i, p i ∈ range γ) :=
begin
  let p' : ℕ → X := λ k, if h : k < n+1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩,
  obtain ⟨γ, hγ⟩ : ∃ (γ : path (p' 0) (p' n)), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s,
  { have hp' : ∀ i ≤ n, p' i ∈ s,
    { intros i hi,
      simp [p', nat.lt_succ_of_le hi, hp] },
    clear_value p',
    clear hp p,
    induction n with n hn,
    { use path.refl (p' 0),
      { split,
        { rintros i hi, rw nat.le_zero_iff.mp hi, exact ⟨0, rfl⟩ },
        { rw range_subset_iff, rintros x, exact hp' 0 (le_refl _) } } },
    { rcases hn (λ i hi, hp' i $ nat.le_succ_of_le hi) with ⟨γ₀, hγ₀⟩,
      rcases h.joined_in (p' n) (p' $ n+1) (hp' n n.le_succ) (hp' (n+1) $ le_refl _) with ⟨γ₁, hγ₁⟩,
      let γ : path (p' 0) (p' $ n+1) := γ₀.trans γ₁,
      use γ,
      have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁,
      split,
      { rintros i hi,
        by_cases hi' : i ≤ n,
        { rw range_eq,
          left,
          exact hγ₀.1 i hi' },
        { rw [not_le, ← nat.succ_le_iff] at hi',
          have : i = n.succ := by linarith,
          rw this,
          use 1,
          exact γ.target } },
      { rw range_eq,
        apply union_subset hγ₀.2,
        rw range_subset_iff,
        exact hγ₁ } } },
  have hpp' : ∀ k < n+1, p k = p' k,
  { intros k hk, simp only [p', hk, dif_pos], congr, ext, rw fin.coe_coe_of_lt hk, norm_cast },
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self),
  simp only [γ.cast_coe],
  refine and.intro hγ.2 _,
  rintros ⟨i, hi⟩,
  convert hγ.1 i (nat.le_of_lt_succ hi), rw ← hpp' i hi,
  congr,
  ext,
  rw fin.coe_coe_of_lt hi,
  norm_cast
end

lemma is_path_connected.exists_path_through_family'
  {X : Type*} [topological_space X] {n : ℕ} {s : set X} (h : is_path_connected s)
  (p : fin (n+1) → X) (hp : ∀ i, p i ∈ s) :
  ∃ (γ : path (p 0) (p n)) (t : fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i :=
begin
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩,
  rcases hγ with ⟨h₁, h₂⟩,
  simp only [range, mem_set_of_eq] at h₂,
  rw range_subset_iff at h₁,
  choose! t ht using h₂,
  exact ⟨γ, t, h₁, ht⟩
end

/-! ### Path connected spaces -/

/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class path_connected_space (X : Type*) [topological_space X] : Prop :=
(nonempty : nonempty X)
(joined : ∀ x y : X, joined x y)

attribute [instance, priority 50] path_connected_space.nonempty

lemma path_connected_space_iff_zeroth_homotopy :
  path_connected_space X ↔ nonempty (zeroth_homotopy X) ∧ subsingleton (zeroth_homotopy X) :=
begin
  letI := path_setoid X,
  split,
  { introI h,
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨_⟩⟩,
    rintros ⟨x⟩ ⟨y⟩,
    exact quotient.sound (path_connected_space.joined x y) },
  { unfold zeroth_homotopy,
    rintros ⟨h, h'⟩,
    resetI,
    exact ⟨(nonempty_quotient_iff _).mp h, λ x y, quotient.exact $ subsingleton.elim ⟦x⟧ ⟦y⟧⟩ },
end

namespace path_connected_space
variables [path_connected_space X]

/-- Use path-connectedness to build a path between two points. -/
def some_path (x y : X) : path x y :=
nonempty.some (joined x y)

end path_connected_space

lemma is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space F :=
begin
  rw is_path_connected_iff,
  split,
  { rintro ⟨⟨x, x_in⟩, h⟩,
    refine ⟨⟨⟨x, x_in⟩⟩, _⟩,
    rintros ⟨y, y_in⟩ ⟨z, z_in⟩,
    have H := h y z y_in z_in,
    rwa joined_in_iff_joined y_in z_in at H },
  { rintros ⟨⟨x, x_in⟩, H⟩,
    refine ⟨⟨x, x_in⟩, λ y z y_in z_in, _⟩,
    rw joined_in_iff_joined y_in z_in,
    apply H }
end

lemma path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X) :=
begin
  split,
  { introI h,
    inhabit X,
    refine ⟨default X, mem_univ _, _⟩,
    simpa using path_connected_space.joined (default X) },
  { intro h,
    have h' := h.joined_in,
    cases h with x h,
    exact ⟨⟨x⟩, by simpa using h'⟩ },
end

lemma path_connected_space_iff_eq : path_connected_space X ↔ ∃ x : X, path_component x = univ :=
by simp [path_connected_space_iff_univ, is_path_connected_iff_eq]

@[priority 100] -- see Note [lower instance priority]
instance path_connected_space.connected_space [path_connected_space X] : connected_space X :=
begin
  rw connected_space_iff_connected_component,
  rcases is_path_connected_iff_eq.mp (path_connected_space_iff_univ.mp ‹_›) with ⟨x, x_in, hx⟩,
  use x,
  rw ← univ_subset_iff,
  exact (by simpa using hx : path_component x = univ) ▸ path_component_subset_component x
end

namespace path_connected_space
variables [path_connected_space X]

lemma exists_path_through_family {n : ℕ} (p : fin (n+1) → X) :
  ∃ γ : path (p 0) (p n), (∀ i, p i ∈ range γ) :=
begin
  have : is_path_connected (univ : set X) := path_connected_space_iff_univ.mp (by apply_instance),
  rcases this.exists_path_through_family p (λ i, true.intro) with ⟨γ, -, h⟩,
  exact ⟨γ, h⟩
end

lemma exists_path_through_family' {n : ℕ} (p : fin (n+1) → X) :
  ∃ (γ : path (p 0) (p n)) (t : fin (n + 1) → I), ∀ i, γ (t i) = p i :=
begin
  have : is_path_connected (univ : set X) := path_connected_space_iff_univ.mp (by apply_instance),
  rcases this.exists_path_through_family' p (λ i, true.intro) with ⟨γ, t, -, h⟩,
  exact ⟨γ, t, h⟩
end

end path_connected_space

/-! ### Locally path connected spaces -/

/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class loc_path_connected_space (X : Type*) [topological_space X] : Prop :=
(path_connected_basis : ∀ x : X, (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s) id)

export loc_path_connected_space (path_connected_basis)

lemma loc_path_connected_of_bases {p : ι → Prop} {s : X → ι → set X}
  (h : ∀ x, (𝓝 x).has_basis p (s x)) (h' : ∀ x i, p i → is_path_connected (s x i)) :
  loc_path_connected_space X :=
begin
  constructor,
  intro x,
  apply (h x).to_has_basis,
  { intros i pi,
    exact ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩, by refl⟩ },
  { rintros U ⟨U_in, hU⟩,
    rcases (h x).mem_iff.mp U_in with ⟨i, pi, hi⟩,
    tauto }
end

lemma path_connected_space_iff_connected_space [loc_path_connected_space X] :
  path_connected_space X ↔ connected_space X :=
begin
  split,
  { introI h,
    apply_instance },
  { introI hX,
    inhabit X,
    let x₀ := default X,
    rw path_connected_space_iff_eq,
    use x₀,
    refine eq_univ_of_nonempty_clopen (by simp) ⟨_, _⟩,
    { rw is_open_iff_mem_nhds,
      intros y y_in,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      apply mem_of_superset U_in,
      rw ← path_component_congr y_in,
      exact hU.subset_path_component (mem_of_mem_nhds U_in) },
    { rw is_closed_iff_nhds,
      intros y H,
      rcases (path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩,
      rcases H U U_in with ⟨z, hz, hz'⟩,
      exact ((hU.joined_in z y hz $ mem_of_mem_nhds U_in).joined.mem_path_component hz') } },
end

lemma path_connected_subset_basis [loc_path_connected_space X] {U : set X} (h : is_open U)
  (hx : x ∈ U) : (𝓝 x).has_basis (λ s : set X, s ∈ 𝓝 x ∧ is_path_connected s ∧ s ⊆ U) id :=
(path_connected_basis x).has_basis_self_subset (is_open.mem_nhds h hx)

lemma loc_path_connected_of_is_open [loc_path_connected_space X] {U : set X} (h : is_open U) :
  loc_path_connected_space U :=
⟨begin
  rintros ⟨x, x_in⟩,
  rw nhds_subtype_eq_comap,
  constructor,
  intros V,
  rw (has_basis.comap (coe : U → X) (path_connected_subset_basis h x_in)).mem_iff,
  split,
  { rintros ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩,
    exact ⟨coe ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩ },
  { rintros ⟨W, ⟨W_in, hW⟩, hWV⟩,
    refine ⟨coe '' W, ⟨filter.image_coe_mem_of_mem_comap (is_open.mem_nhds h x_in) W_in,
                       hW.image continuous_subtype_coe, subtype.coe_image_subset U W⟩, _⟩,
    rintros x ⟨y, ⟨y_in, hy⟩⟩,
    rw ← subtype.coe_injective hy,
    tauto },
end⟩

lemma is_open.is_connected_iff_is_path_connected
  [loc_path_connected_space X] {U : set X} (U_op : is_open U) :
  is_path_connected U ↔ is_connected U :=
begin
  rw [is_connected_iff_connected_space, is_path_connected_iff_path_connected_space],
  haveI := loc_path_connected_of_is_open U_op,
  exact path_connected_space_iff_connected_space
end
