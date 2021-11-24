/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import topology.homotopy.basic
import topology.homotopy.fundamental_groupoid

/-!
# Homotopy groups of a topological space

In this file, we define the homotopy groups of a topological space.
-/

universes u v

variables (ι : Type u)

noncomputable theory

open_locale unit_interval classical

/--
Function used to extend maps from `ι → I` to `ι → R`.

TODO: Generalise to arbitrary products of subtypes
-/
def baz : C(ι → ℝ, ι → I) :=
{ to_fun := λ x i, continuous_map.id.Icc_extend (@zero_le_one ℝ _) (x i) }

lemma baz_apply_of_mem (x : ι → ℝ) (h : x ∈ (set.univ : set ι).pi (λ i, I)) :
  baz ι x = (λ i, ⟨x i, set.mem_univ_pi.1 h _⟩) :=
begin
  ext i,
  rw [baz, continuous_map.coe_mk, continuous_map.coe_Icc_extend, continuous_map.id_coe],
  apply congr_arg,
  rw set.Icc_extend_of_mem _ _ (set.mem_univ_pi.1 h _),
  refl,
end

lemma baz_apply_apply (x : ι → ℝ) (i : ι) :
  baz ι x i = continuous_map.id.Icc_extend (@zero_le_one ℝ _) (x i) := rfl

/--
Higher dimensional "paths"

TODO: Name?
-/
structure foo {X : Type v} [topological_space X] (x : X) extends C(ι → I, X) :=
(boundary : ∀ p : ι → I, (∃ i, p i = 0 ∨ p i = 1) → to_fun p = x)

namespace foo

variable {ι}
variables {X : Type v} [topological_space X] {x₀ : X}

instance : has_coe_to_fun (foo ι x₀) (λ _, (ι → I) → X) := ⟨λ f, f.to_fun⟩

lemma coe_fn_injective : @function.injective (foo ι x₀) ((ι → I) → X) coe_fn :=
begin
  rintros ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h,
  congr' 2,
end

@[simp]
lemma coe_to_continuous_map (f : foo ι x₀) : ⇑(f.to_continuous_map) = f := rfl

@[simp]
lemma coe_mk (f : (ι → I) → X) (h₁ : continuous f)
  (h₂ : ∀ p : ι → I, (∃ i, p i = 0 ∨ p i = 1) → f p = x₀) :
  ⇑(foo.mk ⟨f, h₁⟩ h₂) = f := rfl

@[ext]
lemma ext {f g : foo ι x₀} (h : ∀ i, f i = g i) : f = g :=
coe_fn_injective $ funext h

def extend (f : foo ι x₀) : C(ι → ℝ, X) := f.to_continuous_map.comp (baz ι)

lemma extend_apply_of_mem {f : foo ι x₀} {p : ι → ℝ} (h : p ∈ (set.univ : set ι).pi (λ i, I)) :
  f.extend p = f (λ i, ⟨p i, set.mem_univ_pi.1 h _⟩) :=
begin
  rw [extend, continuous_map.comp_apply, baz_apply_of_mem _ _ h],
  refl,
end

@[continuity]
lemma continuous (f : foo ι x₀) : continuous ⇑f := f.to_continuous_map.continuous

lemma apply_of_exists_eq_zero_or_eq_one {f : foo ι x₀} (p : ι → I) (hx : ∃ i, p i = 0 ∨ p i = 1) :
  f p = x₀ := f.boundary _ hx

/--
The constant "path"
-/
def refl (x₀ : X) : foo ι x₀ :=
{ to_fun := λ i, x₀,
  boundary := λ p hp, rfl }

/--
Reversing `f` along the index `i`
-/
def symm (f : foo ι x₀) (i : ι) : foo ι x₀ :=
{ to_fun := λ t, f (λ j, if i = j then σ (t j) else t j),
  continuous_to_fun := begin
    apply f.continuous.comp,
    rw continuous_pi_iff,
    intro j,
    split_ifs;
    continuity
  end,
  boundary := begin
    rintros p ⟨j, hj⟩,
    dsimp only,
    apply apply_of_exists_eq_zero_or_eq_one,
    use j,
    rcases hj with (hj | hj); rw hj; finish
  end }

/--
Composing `f` and `g` along the index `i`.
-/
def trans (f g : foo ι x₀) (i : ι) : foo ι x₀ :=
{ to_fun := λ t,
  if (t i : ℝ) ≤ 1/2 then
    f.extend (λ j, if i = j then 2 * t j else t j)
  else
    g.extend (λ j, if i = j then 2 * t j - 1 else t j),
  continuous_to_fun := begin
    apply continuous_if_le,
    { continuity },
    { continuity },
    { apply continuous.continuous_on,
      apply continuous.comp,
      { continuity },
      { rw continuous_pi_iff,
        intro j,
        split_ifs;
        continuity } },
    { apply continuous.continuous_on,
      apply continuous.comp,
      { continuity },
      { rw continuous_pi_iff,
        intro j,
        split_ifs;
        continuity } },
    { intros x hx,
      rw [extend_apply_of_mem, extend_apply_of_mem],
      { rw [apply_of_exists_eq_zero_or_eq_one, apply_of_exists_eq_zero_or_eq_one];
        { use i,
          norm_num [hx] } },
      { rw set.mem_pi,
        intros j hj,
        split_ifs,
        { rw [←h, hx],
          norm_num },
        { exact subtype.mem (x j) } },
      { rw set.mem_pi,
        intros j hj,
        split_ifs,
        { rw [←h, hx],
          norm_num },
        { exact subtype.mem (x j) } } }
  end,
  boundary := begin
    rintros p ⟨j, hj⟩,
    dsimp only,
    split_ifs,
    { rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one],
      { use j,
        cases hj,
        { left,
          norm_num [hj] },
        { right,
          apply subtype.ext,
          rw [subtype.coe_mk, if_neg, hj],
          intro hij,
          norm_num [hij, hj] at h } },
      { rw set.mem_pi,
        intros k hk,
        split_ifs with hik hik,
        { rw [unit_interval.mul_pos_mem_iff zero_lt_two, ←hik],
          exact ⟨unit_interval.nonneg _, h⟩ },
        { exact subtype.mem _ } } },
    {  rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one],
      { use j,
        cases hj,
        { left,
          apply subtype.ext,
          rw [subtype.coe_mk, if_neg, hj],
          intro hij,
          norm_num [hij, hj] at h },
        { right,
          norm_num [hj] } },
      { rw set.mem_pi,
        intros k hk,
        split_ifs with hik hik,
        { rw [unit_interval.two_mul_sub_one_mem_iff, ←hik],
          exact ⟨le_of_not_le h, unit_interval.le_one _⟩, },
        { exact subtype.mem _ } } }
  end } .

def reparam (f : foo ι x₀) (g : C(I, I)) (hg₀ : g 0 = 0 ∨ g 0 = 1) (hg₁ : g 1 = 0 ∨ g 1 = 1)
  (i : ι) : foo ι x₀ :=
{ to_fun := λ p, f (λ j, if i = j then g (p j) else p j),
  continuous_to_fun := begin
    apply f.continuous.comp,
    apply continuous_pi,
    intro j,
    split_ifs;
      continuity
  end,
  boundary := λ p hp, begin
    apply apply_of_exists_eq_zero_or_eq_one,
    rcases hp with ⟨j, hj|hj⟩;
    rcases hg₀ with (hg₀ | hg₀);
    rcases hg₁ with (hg₁ | hg₁);
    use j;
    split_ifs;
    simp [hg₀, hg₁, hj]
  end }

/--
Homotopy between `f` and `g`
-/
abbreviation homotopy (f g : foo ι x₀) :=
continuous_map.homotopy_rel f.to_continuous_map g.to_continuous_map {p | ∃ i, p i = 0 ∨ p i = 1}

namespace homotopy

/--
Evaluating `F` at an intermediate point `t` gives us a "path"
-/
def eval {f g : foo ι x₀} (F : homotopy f g) (t : I) : foo ι x₀ :=
{ to_fun := F.to_homotopy.curry t,
  boundary := begin
    intros p hp,
    simp only [continuous_map.homotopy.curry_apply, continuous_map.homotopy_with.coe_to_homotopy],
    rw continuous_map.homotopy_rel.eq_snd,
    { exact g.boundary _ hp },
    exact hp
  end }

@[simp]
lemma eval_zero {f g : foo ι x₀} (F : homotopy f g) : F.eval 0 = f :=
by { ext t, simp [eval] }

@[simp]
lemma eval_one {f g : foo ι x₀} (F : homotopy f g) : F.eval 1 = g :=
by { ext t, simp [eval] }

/--
Constant homotopy
-/
def refl (f : foo ι x₀) : homotopy f f :=
continuous_map.homotopy_rel.refl f.to_continuous_map _

/--
Reversing a homotopy
-/
def symm {f g : foo ι x₀} (F : homotopy f g) : homotopy g f :=
continuous_map.homotopy_rel.symm F

/--
Composing homotopies
-/
def trans {f g h : foo ι x₀} (F : homotopy f g) (G : homotopy g h) : homotopy f h :=
continuous_map.homotopy_rel.trans F G

/--
Horizontal composition, that is, composing homotopic paths gives us a homotopy
-/
def hcomp {f₀ f₁ g₀ g₁ : foo ι x₀} (F : homotopy f₀ g₀) (G : homotopy f₁ g₁) (i : ι) :
  homotopy (f₀.trans f₁ i) (g₀.trans g₁ i) :=
{ to_fun := λ x,
    if (x.2 i : ℝ) ≤ 1/2 then
      (F.eval x.1).extend (λ j, if i = j then 2 * x.2 j else x.2 j)
    else
      (G.eval x.1).extend (λ j, if i = j then 2 * x.2 j - 1 else x.2 j),
  continuous_to_fun := begin
    apply continuous_if_le,
    { exact continuous_induced_dom.comp ((continuous_apply i).comp continuous_snd) },
    { exact continuous_const },
    { apply continuous.continuous_on,
      apply F.to_homotopy.continuous.comp,
      refine continuous_fst.prod_mk (continuous_pi _),
      intros j,
      simp_rw baz_apply_apply,
      split_ifs,
      refine (continuous_map.Icc_extend (@zero_le_one ℝ _) continuous_map.id).continuous.comp
        (continuous_const.mul (continuous_induced_dom.comp
        ((continuous_apply j).comp continuous_snd))),
      refine (continuous_map.Icc_extend (@zero_le_one ℝ _) continuous_map.id).continuous.comp
        (continuous_induced_dom.comp (((continuous_apply j).comp continuous_snd))) },
    { apply continuous.continuous_on,
      apply G.to_homotopy.continuous.comp,
      refine continuous_fst.prod_mk (continuous_pi _),
      intros j,
      simp_rw baz_apply_apply,
      split_ifs,
      refine (continuous_map.Icc_extend (@zero_le_one ℝ _) continuous_map.id).continuous.comp
        ((continuous_const.mul (continuous_induced_dom.comp _)).sub continuous_const),
      exact ((continuous_apply j).comp continuous_snd),
      refine (continuous_map.Icc_extend (@zero_le_one ℝ _) continuous_map.id).continuous.comp
        (continuous_induced_dom.comp _),
      exact (continuous_apply j).comp continuous_snd },
    { intros x hx,
      rw [extend_apply_of_mem, extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one,
          apply_of_exists_eq_zero_or_eq_one],
      { use i, left, norm_num [hx] },
      { use i, right, norm_num [hx] },
      { rw set.mem_univ_pi,
        intro j,
        split_ifs; norm_num [hx, unit_interval.nonneg (x.2 j), unit_interval.le_one (x.2 j), ←h] },
      { rw set.mem_univ_pi,
        intro j,
        split_ifs;
          norm_num [hx, unit_interval.nonneg (x.2 j), unit_interval.le_one (x.2 j), ←h] } }
  end,
  to_fun_zero := λ x, by norm_num [foo.trans],
  to_fun_one := λ x, by norm_num [foo.trans],
  prop' :=
  begin
    rintros t x hx,
    simp_rw [continuous_map.coe_mk, coe_to_continuous_map],
    split_ifs,
    { rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one _ hx,
          apply_of_exists_eq_zero_or_eq_one _ hx, apply_of_exists_eq_zero_or_eq_one],
      { exact ⟨rfl, rfl⟩ },
      { rcases hx with ⟨j, hj|hj⟩,
        { use j, left, norm_num [hj] },
        { use j, right,
          apply subtype.ext,
          simp only [unit_interval.coe_one, subtype.coe_mk],
          rw [if_neg, hj, unit_interval.coe_one],
          intro hij,
          norm_num [hij, hj] at h } },
      { rw set.mem_univ_pi,
        intro j,
        split_ifs with hij hij,
        { exact (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨unit_interval.nonneg _, hij ▸ h⟩ },
        { exact subtype.mem _ } } },
    { rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one _ hx,
          apply_of_exists_eq_zero_or_eq_one _ hx, apply_of_exists_eq_zero_or_eq_one],
      { exact ⟨rfl, rfl⟩ },
      { rcases hx with ⟨j, hj|hj⟩,
        { use j,
          left,
          apply subtype.ext,
          simp only [unit_interval.coe_zero, subtype.coe_mk],
          rw [if_neg, hj, unit_interval.coe_zero],
          intro hij,
          norm_num [hij, hj] at h },
        { use j, right, norm_num [hj] } },
      { rw set.mem_univ_pi,
        intro j,
        split_ifs with hij hij,
        { exact unit_interval.two_mul_sub_one_mem_iff.2
          ⟨hij ▸ le_of_not_le h, unit_interval.le_one _⟩ },
        { exact subtype.mem _ } } }
  end } .

def reparam (f : foo ι x₀) (g : C(I, I)) (hg₀ : g 0 = 0) (hg₁ : g 1 = 1)
  (i : ι) : f.homotopy (f.reparam g (or.inl hg₀) (or.inr hg₁) i) :=
{ to_fun := λ x, f (λ j,
    if i = j then
      ⟨σ x.1 * x.2 j + x.1 * g (x.2 j),
      show (σ x.1 : ℝ) • (x.2 j : ℝ) + (x.1 : ℝ) • (g (x.2 j) : ℝ) ∈ I,
      from convex_Icc _ _ (subtype.mem _) (subtype.mem _) (by unit_interval) (by unit_interval)
        (by simp)⟩
    else
      x.2 j),
  continuous_to_fun := begin
    apply f.continuous.comp,
    apply continuous_pi,
    intro j,
    have : _root_.continuous (λ (x : ↥I × (ι → ↥I)), x.snd j),
      { exact (continuous_apply j).comp continuous_snd },
    split_ifs,
    { continuity },
    { exact this }
  end,
  to_fun_zero := begin
    intro x,
    simp,
  end,
  to_fun_one := begin
    intro x,
    simp,
    refl,
  end,
  prop' := begin
    intros t x hx,
    simp_rw [continuous_map.coe_mk, coe_to_continuous_map],
    rw [apply_of_exists_eq_zero_or_eq_one, apply_of_exists_eq_zero_or_eq_one _ hx,
        apply_of_exists_eq_zero_or_eq_one _ hx],
    { exact ⟨rfl, rfl⟩ },
    rcases hx with ⟨j, hj|hj⟩;
    use j,
    { left, simp [hj, hg₀] },
    { right, simp [hj, hg₁] },
  end } .

end homotopy

end foo
