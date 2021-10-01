/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.unit_interval
import topology.algebra.ordered.proj_Icc
import topology.continuous_function.basic
import topology.compact_open

/-!
# Homotopy between functions

In this file, we define a homotopy between two functions `f₀` and `f₁`. For this, we use a more
general `homotopy_with`, which is inspired by the formalisation of homotopy between functions in
HOL-Analysis. With this, we get `homotopy` as a special case of `homotopy_with`.

## Definitions

* `homotopy_with f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where the intermediate
  maps satisfy the predicate `P : C(X, Y) → Prop`.
* `homotopy_with.refl` is the homotopy between `f₀` and `f₀`.
* `homotopy_with.symm F` is defined by reversing the homotopy `F`
* `homotopy_with.trans F G`, where `F : homotopy f₀ f₁`, `G : homotopy f₁ f₂` is a `homotopy f₀ f₂`
  defined by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
* `homotopy f₀ f₁` is defined to be `homotopy_with f₀ f₁ (λ f, true)`.
* `homotopy.refl` is a variant of `homotopy_with.refl` with the proof of `P f` filled in.
* `homotopy_rel f₀ f₁ S` is defined to be
  `homotopy_with f₀ f₁ (λ f, ∀ x ∈ S, f x = f₀ x ∧ f x = f₁ x)`. That is, a homotopy between `f₀`
  and `f₁` which is fixed on the points in `S`.
* `homotopy_rel.refl` is a variant of `homotopy_with.refl` with the proof of `P f` filled in.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/

noncomputable theory

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

open_locale unit_interval

namespace continuous_map

/--
The type of homotopies between two functions, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`.
-/
structure homotopy_with (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends C(I × X, Y) :=
(to_fun_zero : ∀ x, to_fun (0, x) = f₀ x)
(to_fun_one : ∀ x, to_fun (1, x) = f₁ x)
(prop' : ∀ t, P ⟨λ x, to_fun (t, x),
  continuous.comp continuous_to_fun (continuous_const.prod_mk continuous_id')⟩)

namespace homotopy_with

section

variables {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

instance : has_coe_to_fun (homotopy_with f₀ f₁ P) := ⟨_, λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (homotopy_with f₀ f₁ P) (I × X → Y) coe_fn :=
begin
  rintros ⟨⟨F, _⟩, _⟩ ⟨⟨G, _⟩, _⟩ h,
  congr' 2,
end

@[ext]
lemma ext {F G : homotopy_with f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
coe_fn_injective $ funext h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : homotopy_with f₀ f₁ P) : I × X → Y := F

initialize_simps_projections homotopy_with (to_continuous_map_to_fun -> apply, -to_continuous_map)

@[continuity]
protected lemma continuous (F : homotopy_with f₀ f₁ P) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : homotopy_with f₀ f₁ P) (x : X) : F (0, x) = f₀ x := F.to_fun_zero x

@[simp]
lemma apply_one (F : homotopy_with f₀ f₁ P) (x : X) : F (1, x) = f₁ x := F.to_fun_one x

@[simp]
lemma coe_to_continuous_map (F : homotopy_with f₀ f₁ P) : ⇑F.to_continuous_map = F := rfl

/--
Currying a homotopy to a continuous function fron `I` to `C(X, Y)`.
-/
def curry (F : homotopy_with f₀ f₁ P) : C(I, C(X, Y)) := F.to_continuous_map.curry

lemma prop (F : homotopy_with f₀ f₁ P) (t : I) : P (F.curry t) := F.prop' t

@[simp]
lemma curry_apply (F : homotopy_with f₀ f₁ P) (t : I) (x : X) : F.curry t x = F (t, x) := rfl

/--
Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : homotopy_with f₀ f₁ P) : C(ℝ, C(X, Y)) := F.curry.Icc_extend zero_le_one

lemma extend_apply_of_le_zero (F : homotopy_with f₀ f₁ P) {t : ℝ} (ht : t ≤ 0) (x : X) :
  F.extend t x = f₀ x :=
begin
  rw [←F.apply_zero],
  exact continuous_map.congr_fun (set.Icc_extend_of_le_left (@zero_le_one ℝ _) F.curry ht) x,
end

lemma extend_apply_of_one_le (F : homotopy_with f₀ f₁ P) {t : ℝ} (ht : 1 ≤ t) (x : X) :
  F.extend t x = f₁ x :=
begin
  rw [←F.apply_one],
  exact continuous_map.congr_fun (set.Icc_extend_of_right_le (@zero_le_one ℝ _) F.curry ht) x,
end

@[simp]
lemma extend_apply_coe (F : homotopy_with f₀ f₁ P) (t : I) (x : X) : F.extend t x = F (t, x) :=
continuous_map.congr_fun (set.Icc_extend_coe (@zero_le_one ℝ _) F.curry t) x

@[simp]
lemma extend_apply_of_mem_I (F : homotopy_with f₀ f₁ P) {t : ℝ} (ht : t ∈ I) (x : X) :
  F.extend t x = F (⟨t, ht⟩, x) :=
continuous_map.congr_fun (set.Icc_extend_of_mem (@zero_le_one ℝ _) F.curry ht) x

lemma extend_prop (F : homotopy_with f₀ f₁ P) (t : ℝ) : P (F.extend t) :=
begin
  by_cases ht₀ : 0 ≤ t,
  { by_cases ht₁ : t ≤ 1,
    { convert F.prop ⟨t, ht₀, ht₁⟩,
      ext,
      rw [F.extend_apply_of_mem_I ⟨ht₀, ht₁⟩, F.curry_apply] },
    { convert F.prop 1,
      ext,
      rw [F.extend_apply_of_one_le (le_of_not_le ht₁), F.curry_apply, F.apply_one] } },
  { convert F.prop 0,
    ext,
    rw [F.extend_apply_of_le_zero (le_of_not_le ht₀), F.curry_apply, F.apply_zero] }
end

end

variable {P : C(X, Y) → Prop}

/--
Given a continuous function `f` and a proof `hP : P f`, we can define a `homotopy_with f f` by
`F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) (hP : P f) : homotopy_with f f P :=
{ to_fun := λ x, f x.2,
  continuous_to_fun := by continuity,
  to_fun_zero := λ _, rfl,
  to_fun_one := λ _, rfl,
  prop' := λ t, begin
    convert hP,
    ext, refl,
  end }

instance : inhabited (homotopy_with (continuous_map.id : C(X, X)) continuous_map.id (λ f, true)) :=
⟨homotopy_with.refl continuous_map.id trivial⟩

/--
Given a `homotopy_with f₀ f₁ P`, we can define a `homotopy_with f₁ f₀ P` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : homotopy_with f₁ f₀ P :=
{ to_fun := λ x, F (σ x.1, x.2),
  continuous_to_fun := by continuity,
  to_fun_zero := by norm_num,
  to_fun_one := by norm_num,
  prop' := λ t, by simpa using F.prop' (σ t) }

@[simp]
lemma symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : F.symm.symm = F :=
by { ext, simp }

/--
Given `homotopy_with f₀ f₁ P` and `homotopy_with f₁ f₂ P`, we can define a `homotopy_with f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) :
  homotopy_with f₀ f₂ P :=
{ to_fun := λ x, if (x.1 : ℝ) ≤ 1/2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2,
  continuous_to_fun := begin
    refine continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
      (F.continuous.comp (by continuity)).continuous_on
      (G.continuous.comp (by continuity)).continuous_on _,
    rintros x hx,
    norm_num [hx],
  end,
  to_fun_zero := λ x, by norm_num,
  to_fun_one := λ x, by norm_num,
  prop' := λ t, begin
    simp only,
    split_ifs,
    { exact F.extend_prop _ },
    { exact G.extend_prop _ },
  end }

lemma trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
show ite _ _ _ = _,
by split_ifs; { rw [extend, continuous_map.coe_Icc_extend, set.Icc_extend_of_mem], refl }

lemma symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) :
  (F.trans G).symm = G.symm.trans F.symm :=
begin
  ext x,
  simp only [symm_apply, trans_apply],
  split_ifs with h₁ h₂,
  { change (x.1 : ℝ) ≤ _ at h₂,
    change (1 : ℝ) - x.1 ≤ _ at h₁,
    have ht : (x.1 : ℝ) = 1/2,
    { linarith },
    norm_num [ht] },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { change ¬ (x.1 : ℝ) ≤ _ at h,
    change ¬ (1 : ℝ) - x.1 ≤ _ at h₁,
    exfalso, linarith }
end

end homotopy_with

/--
A `homotopy f₀ f₁` is defined to be a `homotopy_with` where the predicate is always `true`.
-/
abbreviation homotopy (f₀ f₁ : C(X, Y)) := homotopy_with f₀ f₁ (λ f, true)

namespace homotopy

/--
Given a map `f : C(X, Y)`, we can define a `homotopy f f` by setting `F (t, x) = f x` for all `t`.
This is defined using `homotopy_with.refl`, but with the proof filled in.
-/
@[simps]
def refl (f : C(X, Y)) : homotopy f f := homotopy_with.refl f trivial

/--
Given a `homotopy f₀ f₁`, we can define a `homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : homotopy f₁ f₀ := homotopy_with.symm F

@[simp]
lemma symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : F.symm.symm = F :=
homotopy_with.symm_symm F

/--
Given `homotopy f₀ f₁` and `homotopy f₁ f₂`, we can define a `homotopy f₀ f₂`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) : homotopy f₀ f₂ :=
homotopy_with.trans F G

lemma trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
homotopy_with.trans_apply F G x

lemma symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) :
  (F.trans G).symm = G.symm.trans F.symm :=
homotopy_with.symm_trans F G

end homotopy

/--
A `homotopy_rel f₀ f₁ S` is a homotopy bewteen `f₀` and `f₁` which is fixed on the points in `S`.
-/
abbreviation homotopy_rel (f₀ f₁ : C(X, Y)) (S : set X) :=
homotopy_with f₀ f₁ (λ f, ∀ x ∈ S, f x = f₀ x ∧ f x = f₁ x)

namespace homotopy_rel

section

variables {f₀ f₁ : C(X, Y)} {S : set X}

lemma eq_fst (F : homotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) :
  F (t, x) = f₀ x := (F.prop t x hx).1

lemma eq_snd (F : homotopy_rel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) :
  F (t, x) = f₁ x := (F.prop t x hx).2

lemma fst_eq_snd (F : homotopy_rel f₀ f₁ S) {x : X} (hx : x ∈ S) :
  f₀ x = f₁ x := F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variables {f₀ f₁ f₂ : C(X, Y)} {S : set X}

/--
Given a map `f : C(X, Y)` and a set `S`, we can define a `homotopy_rel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `homotopy_with.refl`, but with the proof
filled in.
-/
@[simps]
def refl (f : C(X, Y)) (S : set X) : homotopy_rel f f S :=
homotopy_with.refl f (λ x hx, ⟨rfl, rfl⟩)

/--
Given a `homotopy_rel f₀ f₁ S`, we can define a `homotopy_rel f₁ f₀ S` by reversing the homotopy.
-/
@[simps]
def symm (F : homotopy_rel f₀ f₁ S) : homotopy_rel f₁ f₀ S :=
{ prop' := λ t x hx, by simp [F.eq_snd _ hx, F.fst_eq_snd hx],
  ..homotopy_with.symm F }

@[simp]
lemma symm_symm (F : homotopy_rel f₀ f₁ S) : F.symm.symm = F :=
homotopy_with.symm_symm F

/--
Given `homotopy_rel f₀ f₁ S` and `homotopy_rel f₁ f₂ S`, we can define a `homotopy_rel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) : homotopy_rel f₀ f₂ S :=
{ to_fun := λ x, if (x.1 : ℝ) ≤ 1/2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2,
  continuous_to_fun := begin
    refine continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
      (F.continuous.comp (by continuity)).continuous_on
      (G.continuous.comp (by continuity)).continuous_on _,
    rintros x hx,
    norm_num [hx],
  end,
  to_fun_zero := λ x, by norm_num,
  to_fun_one := λ x, by norm_num,
  prop' := λ t, begin
    simp only,
    split_ifs,
    { intros x hx,
      simp [(homotopy_with.extend_prop F (2 * t) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] },
    { intros x hx,
      simp [(homotopy_with.extend_prop G (2 * t - 1) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] },
  end }

lemma trans_apply (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
show ite _ _ _ = _,
by split_ifs;
  { rw [homotopy_with.extend, continuous_map.coe_Icc_extend, set.Icc_extend_of_mem], refl }

lemma symm_trans (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) :
  (F.trans G).symm = G.symm.trans F.symm :=
begin
  ext x,
  simp only [symm_apply, trans_apply],
  split_ifs with h₁ h₂,
  { change (x.1 : ℝ) ≤ _ at h₂,
    change (1 : ℝ) - x.1 ≤ _ at h₁,
    have ht : (x.1 : ℝ) = 1/2,
    { linarith },
    norm_num [ht] },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { change ¬ (x.1 : ℝ) ≤ _ at h,
    change ¬ (1 : ℝ) - x.1 ≤ _ at h₁,
    exfalso, linarith }
end

end homotopy_rel

end continuous_map
