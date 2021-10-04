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

In this file, we define a homotopy between two functions `f₀` and `f₁`. First we define `homotopy`
between the two functions, with no restrictions on the intermediate maps. Then, as in the
formalisation in HOL-Analysis, we define `homotopy_with f₀ f₁ P`, for homotopies between `f₀` and
`f₁`, where the intermediate maps satisfy the predicate `P`. Finally, we define
`homotopy_rel f₀ f₁ S`, for homotopies between `f₀` and `f₁` which are fixed on `S`.

## Definitions

* `homotopy f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`.
* `homotopy_with f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where the intermediate
  maps satisfy the predicate `P`.
* `homotopy_rel f₀ f₁ S` is the type of homotopies between `f₀` and `f₁` which are fixed on `S`.

For each of the above, we have

* `refl f`, which is the constant homotopy from `f` to `f`.
* `symm F`, which reverses the homotopy `F`. For example, if `F : homotopy f₀ f₁`, then
  `F.symm : homotopy f₁ f₀`.
* `trans F G`, which concatenates the homotopies `F` and `G`. For example, if `F : homotopy f₀ f₁`
  and `G : homotopy f₁ f₂`, then `F.trans G : homotopy f₀ f₂`.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/

noncomputable theory

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

open_locale unit_interval

namespace continuous_map

/--
The type of homotopies between two functions.
-/
structure homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) :=
(to_fun_zero : ∀ x, to_fun (0, x) = f₀ x)
(to_fun_one : ∀ x, to_fun (1, x) = f₁ x)

namespace homotopy

section

variables {f₀ f₁ : C(X, Y)}

instance : has_coe_to_fun (homotopy f₀ f₁) := ⟨_, λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (homotopy f₀ f₁) (I × X → Y) coe_fn :=
begin
  rintros ⟨⟨F, _⟩, _⟩ ⟨⟨G, _⟩, _⟩ h,
  congr' 2,
end

@[ext]
lemma ext {F G : homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
coe_fn_injective $ funext h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : homotopy f₀ f₁) : I × X → Y := F

initialize_simps_projections homotopy (to_continuous_map_to_fun -> apply, -to_continuous_map)

@[continuity]
protected lemma continuous (F : homotopy f₀ f₁) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x := F.to_fun_zero x

@[simp]
lemma apply_one (F : homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x := F.to_fun_one x

@[simp]
lemma coe_to_continuous_map (F : homotopy f₀ f₁) : ⇑F.to_continuous_map = F := rfl

/--
Currying a homotopy to a continuous function fron `I` to `C(X, Y)`.
-/
def curry (F : homotopy f₀ f₁) : C(I, C(X, Y)) := F.to_continuous_map.curry

-- lemma prop (F : homotopy f₀ f₁) (t : I) : P (F.curry t) := F.prop' t

@[simp]
lemma curry_apply (F : homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) := rfl

/--
Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : homotopy f₀ f₁) : C(ℝ, C(X, Y)) := F.curry.Icc_extend zero_le_one

lemma extend_apply_of_le_zero (F : homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) :
  F.extend t x = f₀ x :=
begin
  rw [←F.apply_zero],
  exact continuous_map.congr_fun (set.Icc_extend_of_le_left (@zero_le_one ℝ _) F.curry ht) x,
end

lemma extend_apply_of_one_le (F : homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) :
  F.extend t x = f₁ x :=
begin
  rw [←F.apply_one],
  exact continuous_map.congr_fun (set.Icc_extend_of_right_le (@zero_le_one ℝ _) F.curry ht) x,
end

@[simp]
lemma extend_apply_coe (F : homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
continuous_map.congr_fun (set.Icc_extend_coe (@zero_le_one ℝ _) F.curry t) x

@[simp]
lemma extend_apply_of_mem_I (F : homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) :
  F.extend t x = F (⟨t, ht⟩, x) :=
continuous_map.congr_fun (set.Icc_extend_of_mem (@zero_le_one ℝ _) F.curry ht) x

lemma congr_fun {F G : homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
continuous_map.congr_fun (congr_arg _ h) x

lemma congr_arg (F : homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
F.to_continuous_map.congr_arg h

end

/--
Given a continuous function `f`, we can define a `homotopy f f` by `F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) : homotopy f f :=
{ to_fun := λ x, f x.2,
  continuous_to_fun := by continuity,
  to_fun_zero := λ _, rfl,
  to_fun_one := λ _, rfl }

instance : inhabited (homotopy (continuous_map.id : C(X, X)) continuous_map.id) :=
⟨homotopy.refl continuous_map.id⟩

/--
Given a `homotopy f₀ f₁`, we can define a `homotopy f₁ f₀` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : homotopy f₁ f₀ :=
{ to_fun := λ x, F (σ x.1, x.2),
  continuous_to_fun := by continuity,
  to_fun_zero := by norm_num,
  to_fun_one := by norm_num }

@[simp]
lemma symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : F.symm.symm = F :=
by { ext, simp }

/--
Given `homotopy f₀ f₁` and `homotopy f₁ f₂`, we can define a `homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) :
  homotopy f₀ f₂ :=
{ to_fun := λ x, if (x.1 : ℝ) ≤ 1/2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2,
  continuous_to_fun := begin
    refine continuous_if_le (continuous_induced_dom.comp continuous_fst) continuous_const
      (F.continuous.comp (by continuity)).continuous_on
      (G.continuous.comp (by continuity)).continuous_on _,
    rintros x hx,
    norm_num [hx],
  end,
  to_fun_zero := λ x, by norm_num,
  to_fun_one := λ x, by norm_num }

lemma trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
show ite _ _ _ = _,
by split_ifs; { rw [extend, continuous_map.coe_Icc_extend, set.Icc_extend_of_mem], refl }

lemma symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) :
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

end homotopy

/--
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
structure homotopy_with (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends homotopy f₀ f₁ :=
(prop' : ∀ t, P ⟨λ x, to_fun (t, x),
  continuous.comp continuous_to_fun (continuous_const.prod_mk continuous_id')⟩)

namespace homotopy_with

section

variables {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

instance : has_coe_to_fun (homotopy_with f₀ f₁ P) := ⟨_, λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (homotopy_with f₀ f₁ P) (I × X → Y) coe_fn :=
begin
  rintros ⟨⟨⟨F, _⟩, _⟩, _⟩ ⟨⟨⟨G, _⟩, _⟩, _⟩ h,
  congr' 3,
end

@[ext]
lemma ext {F G : homotopy_with f₀ f₁ P} (h : ∀ x, F x = G x) : F = G :=
coe_fn_injective $ funext h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (F : homotopy_with f₀ f₁ P) : I × X → Y := F

initialize_simps_projections homotopy_with
  (to_homotopy_to_continuous_map_to_fun -> apply, -to_homotopy_to_continuous_map)

@[continuity]
protected lemma continuous (F : homotopy_with f₀ f₁ P) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : homotopy_with f₀ f₁ P) (x : X) : F (0, x) = f₀ x := F.to_fun_zero x

@[simp]
lemma apply_one (F : homotopy_with f₀ f₁ P) (x : X) : F (1, x) = f₁ x := F.to_fun_one x

@[simp]
lemma coe_to_continuous_map (F : homotopy_with f₀ f₁ P) : ⇑F.to_continuous_map = F := rfl

@[simp]
lemma coe_to_homotopy (F : homotopy_with f₀ f₁ P) : ⇑F.to_homotopy = F := rfl

lemma prop (F : homotopy_with f₀ f₁ P) (t : I) : P (F.to_homotopy.curry t) := F.prop' t

lemma extend_prop (F : homotopy_with f₀ f₁ P) (t : ℝ) : P (F.to_homotopy.extend t) :=
begin
  by_cases ht₀ : 0 ≤ t,
  { by_cases ht₁ : t ≤ 1,
    { convert F.prop ⟨t, ht₀, ht₁⟩,
      ext,
      rw [F.to_homotopy.extend_apply_of_mem_I ⟨ht₀, ht₁⟩, F.to_homotopy.curry_apply] },
    { convert F.prop 1,
      ext,
      rw [F.to_homotopy.extend_apply_of_one_le (le_of_not_le ht₁), F.to_homotopy.curry_apply,
          F.to_homotopy.apply_one] } },
  { convert F.prop 0,
    ext,
    rw [F.to_homotopy.extend_apply_of_le_zero (le_of_not_le ht₀), F.to_homotopy.curry_apply,
        F.to_homotopy.apply_zero] }
end

end

variable {P : C(X, Y) → Prop}

/--
Given a continuous function `f`, and a proof `h : P f`, we can define a `homotopy_with f f P` by
`F (t, x) = f x`
-/
@[simps]
def refl (f : C(X, Y)) (hf : P f) : homotopy_with f f P :=
{ prop' := λ t, by { convert hf, cases f, refl },
  ..homotopy.refl f }

instance : inhabited (homotopy_with (continuous_map.id : C(X, X)) continuous_map.id (λ f, true)) :=
⟨homotopy_with.refl _ trivial⟩

/--
Given a `homotopy_with f₀ f₁ P`, we can define a `homotopy_with f₁ f₀ P` by reversing the homotopy.
-/
@[simps]
def symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : homotopy_with f₁ f₀ P :=
{ prop' := λ t, by simpa using F.prop (σ t),
  ..F.to_homotopy.symm }

@[simp]
lemma symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy_with f₀ f₁ P) : F.symm.symm = F :=
ext $ homotopy.congr_fun $ homotopy.symm_symm _

/--
Given `homotopy_with f₀ f₁ P` and `homotopy_with f₁ f₂ P`, we can define a `homotopy_with f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) :
  homotopy_with f₀ f₂ P :=
{ prop' := λ t, begin
    simp only [homotopy.trans],
    change P ⟨λ _, ite ((t : ℝ) ≤ _) _ _, _⟩,
    split_ifs,
    { exact F.extend_prop _ },
    { exact G.extend_prop _ }
  end,
  ..F.to_homotopy.trans G.to_homotopy }

lemma trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
homotopy.trans_apply _ _ _

lemma symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy_with f₀ f₁ P) (G : homotopy_with f₁ f₂ P) :
  (F.trans G).symm = G.symm.trans F.symm :=
ext $ homotopy.congr_fun $ homotopy.symm_trans _ _

end homotopy_with

/--
A `homotopy_rel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
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
{ prop' := λ t, begin
    intros x hx,
    simp only [homotopy.trans],
    change (⟨λ _, ite ((t : ℝ) ≤ _) _ _, _⟩ : C(X, Y)) _ = _ ∧ _ = _,
    split_ifs,
    { simp [(homotopy_with.extend_prop F (2 * t) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] },
    { simp [(homotopy_with.extend_prop G (2 * t - 1) x hx).1, F.fst_eq_snd hx, G.fst_eq_snd hx] },
  end,
  ..homotopy.trans F.to_homotopy G.to_homotopy }

lemma trans_apply (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S)
  (x : I × X) : (F.trans G) x =
  if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
homotopy.trans_apply _ _ _

lemma symm_trans (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel f₁ f₂ S) :
  (F.trans G).symm = G.symm.trans F.symm :=
homotopy_with.ext $ homotopy.congr_fun $ homotopy.symm_trans _ _

end homotopy_rel

end continuous_map
