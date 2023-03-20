/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import algebra.module.linear_map
import linear_algebra.basis.bilinear
import linear_algebra.bilinear_map
import algebra.euclidean_domain.instances
import ring_theory.non_zero_divisors

/-!
# Sesquilinear form

This files provides properties about sesquilinear forms. The maps considered are of the form
`M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁` and `M₂` is a module over `R₂`.
Sesquilinear forms are the special case that `M₁ = M₂`, `R₁ = R₂ = R`, and `I₁ = ring_hom.id R`.
Taking additionally `I₂ = ring_hom.id R`, then one obtains bilinear forms.

These forms are a special case of the bilinear maps defined in `bilinear_map.lean` and all basic
lemmas about construction and elementary calculations are found there.

## Main declarations

* `is_ortho`: states that two vectors are orthogonal with respect to a sesquilinear form
* `is_symm`, `is_alt`: states that a sesquilinear form is symmetric and alternating, respectively
* `orthogonal_bilin`: provides the orthogonal complement with respect to sesquilinear form

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/

open_locale big_operators

variables {R R₁ R₂ R₃ M M₁ M₂ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace linear_map

/-! ### Orthogonal vectors -/

section comm_ring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables [comm_semiring R] [comm_semiring R₁] [add_comm_monoid M₁] [module R₁ M₁]
  [comm_semiring R₂] [add_comm_monoid M₂] [module R₂ M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x y) : Prop := B x y = 0

lemma is_ortho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} {x y} : B.is_ortho x y ↔ B x y = 0 := iff.rfl

lemma is_ortho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : is_ortho B (0 : M₁) x :=
by { dunfold is_ortho, rw [ map_zero B, zero_apply] }

lemma is_ortho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : is_ortho B x (0 : M₂) :=
map_zero (B x)

lemma is_ortho_flip {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {x y} :
  B.is_ortho x y ↔ B.flip.is_ortho y x :=
by simp_rw [is_ortho_def, flip_apply]

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def is_Ortho (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) (v : n → M₁) : Prop :=
pairwise (B.is_ortho on v)

lemma is_Ortho_def {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {v : n → M₁} :
  B.is_Ortho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 := iff.rfl

lemma is_Ortho_flip (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) {v : n → M₁} :
  B.is_Ortho v ↔ B.flip.is_Ortho v :=
begin
  simp_rw is_Ortho_def,
  split; intros h i j hij,
  { rw flip_apply,
    exact h j i (ne.symm hij) },
  simp_rw flip_apply at h,
  exact h j i (ne.symm hij),
end

end comm_ring
section field

variables [field K] [field K₁] [add_comm_group V₁] [module K₁ V₁]
  [field K₂] [add_comm_group V₂] [module K₂ V₂]
  {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K}
  {J₁ : K →+* K} {J₂ : K →+* K}

-- todo: this also holds for [comm_ring R] [is_domain R] when J₁ is invertible
lemma ortho_smul_left {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₁} (ha : a ≠ 0) :
  (is_ortho B x y) ↔ (is_ortho B (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smulₛₗ₂, H, smul_zero]},
  { rw [map_smulₛₗ₂, smul_eq_zero] at H,
    cases H,
    { rw map_eq_zero I₁ at H, trivial },
    { exact H }}
end

-- todo: this also holds for [comm_ring R] [is_domain R] when J₂ is invertible
lemma ortho_smul_right {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] K} {x y} {a : K₂} {ha : a ≠ 0} :
(is_ortho B x y) ↔ (is_ortho B x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smulₛₗ, H, smul_zero] },
  { rw [map_smulₛₗ, smul_eq_zero] at H,
    cases H,
    { simp at H,
      exfalso,
      exact ha H },
    { exact H }}
end

/-- A set of orthogonal vectors `v` with respect to some sesquilinear form `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
lemma linear_independent_of_is_Ortho {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] K} {v : n → V₁}
  (hv₁ : B.is_Ortho v) (hv₂ : ∀ i, ¬ B.is_ortho (v i) (v i)) : linear_independent K₁ v :=
begin
  classical,
  rw linear_independent_iff',
  intros s w hs i hi,
  have : B (s.sum $ λ (i : n), w i • v i) (v i) = 0,
  { rw [hs, map_zero, zero_apply] },
  have hsum : s.sum (λ (j : n), I₁(w j) * B (v j) (v i)) = I₁(w i) * B (v i) (v i),
  { apply finset.sum_eq_single_of_mem i hi,
    intros j hj hij,
    rw [is_Ortho_def.1 hv₁ _ _ hij, mul_zero], },
  simp_rw [B.map_sum₂, map_smulₛₗ₂, smul_eq_mul, hsum] at this,
  apply (map_eq_zero I₁).mp,
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this,
end

end field


/-! ### Reflexive bilinear forms -/

section reflexive

variables [comm_semiring R] [comm_semiring R₁] [add_comm_monoid M₁] [module R₁ M₁]
  {I₁ : R₁ →+* R} {I₂ : R₁ →+* R}
  {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The proposition that a sesquilinear form is reflexive -/
def is_refl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop :=
  ∀ (x y), B x y = 0 → B y x = 0

namespace is_refl

variable (H : B.is_refl)

lemma eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

lemma dom_restrict_refl (H : B.is_refl) (p : submodule R₁ M₁) : (B.dom_restrict₁₂ p p).is_refl :=
λ _ _, by { simp_rw dom_restrict₁₂_apply, exact H _ _}

@[simp] lemma flip_is_refl_iff : B.flip.is_refl ↔ B.is_refl :=
⟨λ h x y H, h y x ((B.flip_apply _ _).trans H), λ h x y, h y x⟩

lemma ker_flip_eq_bot (H : B.is_refl) (h : B.ker = ⊥) : B.flip.ker = ⊥ :=
begin
  refine ker_eq_bot'.mpr (λ _ hx, ker_eq_bot'.mp h _ _),
  ext,
  exact H _ _ (linear_map.congr_fun hx _),
end

lemma ker_eq_bot_iff_ker_flip_eq_bot (H : B.is_refl) : B.ker = ⊥ ↔ B.flip.ker = ⊥ :=
begin
  refine ⟨ker_flip_eq_bot H, λ h, _⟩,
  exact (congr_arg _ B.flip_flip.symm).trans (ker_flip_eq_bot (flip_is_refl_iff.mpr H) h),
end


end is_refl
end reflexive

/-! ### Symmetric bilinear forms -/

section symmetric

variables [comm_semiring R] [add_comm_monoid M] [module R M]
  {I : R →+* R} {B : M →ₛₗ[I] M →ₗ[R] R}

/-- The proposition that a sesquilinear form is symmetric -/
def is_symm (B : M →ₛₗ[I] M →ₗ[R] R) : Prop :=
  ∀ (x y), I (B x y) = B y x

namespace is_symm

protected lemma eq (H : B.is_symm) (x y) : I (B x y) = B y x := H x y

lemma is_refl (H : B.is_symm) : B.is_refl := λ x y H1, by { rw ←H.eq, simp [H1] }

lemma ortho_comm (H : B.is_symm) {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

lemma dom_restrict_symm (H : B.is_symm) (p : submodule R M) : (B.dom_restrict₁₂ p p).is_symm :=
λ _ _, by { simp_rw dom_restrict₁₂_apply, exact H _ _}

end is_symm

lemma is_symm_iff_eq_flip {B : M →ₗ[R] M →ₗ[R] R} : B.is_symm ↔ B = B.flip :=
begin
  split; intro h,
  { ext,
    rw [←h, flip_apply, ring_hom.id_apply] },
  intros x y,
  conv_lhs { rw h },
  rw [flip_apply, ring_hom.id_apply],
end

end symmetric


/-! ### Alternating bilinear forms -/

section alternating

variables [comm_ring R] [comm_semiring R₁] [add_comm_monoid M₁] [module R₁ M₁]
  {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The proposition that a sesquilinear form is alternating -/
def is_alt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : Prop := ∀ x, B x x = 0

namespace is_alt

variable (H : B.is_alt)
include H

lemma self_eq_zero (x) : B x x = 0 := H x

lemma neg (x y) : - B x y = B y x :=
begin
  have H1 : B (y + x) (y + x) = 0,
  { exact self_eq_zero H (y + x) },
  simp [map_add, self_eq_zero H] at H1,
  rw [add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

lemma is_refl : B.is_refl :=
begin
  intros x y h,
  rw [←neg H, h, neg_zero],
end

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

end is_alt

lemma is_alt_iff_eq_neg_flip  [no_zero_divisors R] [char_zero R] {B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] R} :
  B.is_alt ↔ B = -B.flip :=
begin
  split; intro h,
  { ext,
    simp_rw [neg_apply, flip_apply],
    exact (h.neg _ _).symm },
  intros x,
  let h' := congr_fun₂ h x x,
  simp only [neg_apply, flip_apply, ←add_eq_zero_iff_eq_neg] at h',
  exact add_self_eq_zero.mp h',
end

end alternating

end linear_map

namespace submodule

/-! ### The orthogonal complement -/

variables [comm_ring R] [comm_ring R₁] [add_comm_group M₁] [module R₁ M₁]
  {I₁ : R₁ →+* R} {I₂ : R₁ →+* R}
  {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R}

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal_bilin (N : submodule R₁ M₁) (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] R) : submodule R₁ M₁ :=
{ carrier := { m | ∀ n ∈ N, B.is_ortho n m },
  zero_mem' := λ x _, B.is_ortho_zero_right x,
  add_mem' := λ x y hx hy n hn,
    by rw [linear_map.is_ortho, map_add, show B n x = 0, by exact hx n hn,
        show B n y = 0, by exact hy n hn, zero_add],
  smul_mem' := λ c x hx n hn,
    by rw [linear_map.is_ortho, linear_map.map_smulₛₗ, show B n x = 0, by exact hx n hn,
        smul_zero] }

variables {N L : submodule R₁ M₁}

@[simp] lemma mem_orthogonal_bilin_iff {m : M₁} :
  m ∈ N.orthogonal_bilin B ↔ ∀ n ∈ N, B.is_ortho n m := iff.rfl

lemma orthogonal_bilin_le (h : N ≤ L) : L.orthogonal_bilin B ≤ N.orthogonal_bilin B :=
λ _ hn l hl, hn l (h hl)

lemma le_orthogonal_bilin_orthogonal_bilin (b : B.is_refl) :
  N ≤ (N.orthogonal_bilin B).orthogonal_bilin B :=
λ n hn m hm, b _ _ (hm n hn)

end submodule

namespace linear_map

section orthogonal

variables [field K] [add_comm_group V] [module K V]
  [field K₁] [add_comm_group V₁] [module K₁ V₁]
  {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
lemma span_singleton_inf_orthogonal_eq_bot
  (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] K) (x : V₁) (hx : ¬ B.is_ortho x x) :
  (K₁ ∙ x) ⊓ submodule.orthogonal_bilin (K₁ ∙ x) B = ⊥ :=
begin
  rw ← finset.coe_singleton,
  refine eq_bot_iff.2 (λ y h, _),
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩,
  have := h.2 x _,
  { rw finset.sum_singleton at this ⊢,
    suffices hμzero : μ x = 0,
    { rw [hμzero, zero_smul, submodule.mem_bot] },
    change B x (μ x • x) = 0 at this, rw [map_smulₛₗ, smul_eq_mul] at this,
    exact or.elim (zero_eq_mul.mp this.symm)
    (λ y, by { simp at y, exact y })
    (λ hfalse, false.elim $ hx hfalse) },
  { rw submodule.mem_span; exact λ _ hp, hp $ finset.mem_singleton_self _ }
end

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
lemma orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] K} (x : V) :
  submodule.orthogonal_bilin (K ∙ x) B = (B x).ker :=
begin
  ext y,
  simp_rw [submodule.mem_orthogonal_bilin_iff, linear_map.mem_ker,
           submodule.mem_span_singleton ],
  split,
  { exact λ h, h x ⟨1, one_smul _ _⟩ },
  { rintro h _ ⟨z, rfl⟩,
    rw [is_ortho, map_smulₛₗ₂, smul_eq_zero],
    exact or.intro_right _ h }
end


-- todo: Generalize this to sesquilinear maps
lemma span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K}
  {x : V} (hx : ¬ B.is_ortho x x) :
  (K ∙ x) ⊔ submodule.orthogonal_bilin (K ∙ x) B = ⊤ :=
begin
  rw orthogonal_span_singleton_eq_to_lin_ker,
  exact (B x).span_singleton_sup_ker_eq_top hx,
end


-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
lemma is_compl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K}
  {x : V} (hx : ¬ B.is_ortho x x) : is_compl (K ∙ x) (submodule.orthogonal_bilin (K ∙ x) B) :=
{ disjoint := disjoint_iff.2 $ span_singleton_inf_orthogonal_eq_bot B x hx,
  codisjoint := codisjoint_iff.2 $ span_singleton_sup_orthogonal_eq_top hx }

end orthogonal

/-! ### Adjoint pairs -/

section adjoint_pair

section add_comm_monoid

variables [comm_semiring R]
variables [add_comm_monoid M] [module R M]
variables [add_comm_monoid M₁] [module R M₁]
variables [add_comm_monoid M₂] [module R M₂]
variables {I : R →+* R}
variables {B F : M →ₗ[R] M →ₛₗ[I] R} {B' : M₁ →ₗ[R] M₁ →ₛₗ[I] R} {B'' : M₂ →ₗ[R] M₂ →ₛₗ[I] R}
variables {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}

variables (B B' f g)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def is_adjoint_pair := ∀ x y, B' (f x) y = B x (g y)

variables {B B' f g}

lemma is_adjoint_pair_iff_comp_eq_compl₂ :
  is_adjoint_pair B B' f g ↔ B'.comp f = B.compl₂ g :=
begin
  split; intros h,
  { ext x y, rw [comp_apply, compl₂_apply], exact h x y },
  { intros _ _, rw [←compl₂_apply, ←comp_apply, h] },
end

lemma is_adjoint_pair_zero : is_adjoint_pair B B' 0 0 :=
λ _ _, by simp only [zero_apply, map_zero]

lemma is_adjoint_pair_id : is_adjoint_pair B B 1 1 := λ x y, rfl

lemma is_adjoint_pair.add (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B B' f' g') :
  is_adjoint_pair B B' (f + f') (g + g') :=
λ x _, by rw [f.add_apply, g.add_apply, B'.map_add₂, (B x).map_add, h, h']

lemma is_adjoint_pair.comp {f' : M₁ →ₗ[R] M₂} {g' : M₂ →ₗ[R] M₁}
  (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B' B'' f' g') :
  is_adjoint_pair B B'' (f'.comp f) (g.comp g') :=
λ _ _, by rw [linear_map.comp_apply, linear_map.comp_apply, h', h]

lemma is_adjoint_pair.mul
  {f g f' g' : module.End R M} (h : is_adjoint_pair B B f g) (h' : is_adjoint_pair B B f' g') :
  is_adjoint_pair B B (f * f') (g' * g) :=
h'.comp h

end add_comm_monoid

section add_comm_group

variables [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group M₁] [module R M₁]
variables {B F : M →ₗ[R] M →ₗ[R] R} {B' : M₁ →ₗ[R] M₁ →ₗ[R] R}
variables {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}

lemma is_adjoint_pair.sub (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B B' f' g') :
  is_adjoint_pair B B' (f - f') (g - g') :=
λ x _, by rw [f.sub_apply, g.sub_apply, B'.map_sub₂, (B x).map_sub, h, h']

lemma is_adjoint_pair.smul (c : R) (h : is_adjoint_pair B B' f g) :
  is_adjoint_pair B B' (c • f) (c • g) :=
λ _ _, by simp only [smul_apply, map_smul, smul_eq_mul, h _ _]

end add_comm_group

end adjoint_pair

/-! ### Self-adjoint pairs-/

section selfadjoint_pair

section add_comm_monoid

variables [comm_semiring R]
variables [add_comm_monoid M] [module R M]
variables {I : R →+* R}
variables (B F : M →ₗ[R] M →ₛₗ[I] R)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def is_pair_self_adjoint (f : module.End R M) := is_adjoint_pair B F f f

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
protected def is_self_adjoint (f : module.End R M) := is_adjoint_pair B B f f

end add_comm_monoid

section add_comm_group

variables [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group M₁] [module R M₁]
(B F : M →ₗ[R] M →ₗ[R] R)

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def is_pair_self_adjoint_submodule : submodule R (module.End R M) :=
{ carrier   := { f | is_pair_self_adjoint B F f },
  zero_mem' := is_adjoint_pair_zero,
  add_mem'  := λ f g hf hg, hf.add hg,
  smul_mem' := λ c f h, h.smul c, }

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def is_skew_adjoint (f : module.End R M) := is_adjoint_pair B B f (-f)

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def self_adjoint_submodule := is_pair_self_adjoint_submodule B B

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skew_adjoint_submodule := is_pair_self_adjoint_submodule (-B) B

variables {B F}

@[simp] lemma mem_is_pair_self_adjoint_submodule (f : module.End R M) :
  f ∈ is_pair_self_adjoint_submodule B F ↔ is_pair_self_adjoint B F f :=
iff.rfl

lemma is_pair_self_adjoint_equiv (e : M₁ ≃ₗ[R] M) (f : module.End R M) :
  is_pair_self_adjoint B F f ↔
    is_pair_self_adjoint (B.compl₁₂ ↑e ↑e) (F.compl₁₂ ↑e ↑e) (e.symm.conj f) :=
begin
  have hₗ : (F.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).comp (e.symm.conj f) =
    (F.comp f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) :=
  by { ext, simp only [linear_equiv.symm_conj_apply, coe_comp, linear_equiv.coe_coe, compl₁₂_apply,
    linear_equiv.apply_symm_apply], },
  have hᵣ : (B.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).compl₂ (e.symm.conj f) =
    (B.compl₂ f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) :=
  by { ext, simp only [linear_equiv.symm_conj_apply, compl₂_apply, coe_comp, linear_equiv.coe_coe,
      compl₁₂_apply, linear_equiv.apply_symm_apply] },
  have he : function.surjective (⇑(↑e : M₁ →ₗ[R] M) : M₁ → M) := e.surjective,
  simp_rw [is_pair_self_adjoint, is_adjoint_pair_iff_comp_eq_compl₂, hₗ, hᵣ,
    compl₁₂_inj he he],
end

lemma is_skew_adjoint_iff_neg_self_adjoint (f : module.End R M) :
  B.is_skew_adjoint f ↔ is_adjoint_pair (-B) B f f :=
show (∀ x y, B (f x) y = B x ((-f) y)) ↔ ∀ x y, B (f x) y = (-B) x (f y),
by simp

@[simp] lemma mem_self_adjoint_submodule (f : module.End R M) :
  f ∈ B.self_adjoint_submodule ↔ B.is_self_adjoint f := iff.rfl

@[simp] lemma mem_skew_adjoint_submodule (f : module.End R M) :
  f ∈ B.skew_adjoint_submodule ↔ B.is_skew_adjoint f :=
by { rw is_skew_adjoint_iff_neg_self_adjoint, exact iff.rfl }

end add_comm_group

end selfadjoint_pair

/-! ### Nondegenerate bilinear forms -/

section nondegenerate

section comm_semiring
variables [comm_semiring R] [comm_semiring R₁] [add_comm_monoid M₁] [module R₁ M₁]
  [comm_semiring R₂] [add_comm_monoid M₂] [module R₂ M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- A bilinear form is called left-separating if
the only element that is left-orthogonal to every other element is `0`; i.e.,
for every nonzero `x` in `M₁`, there exists `y` in `M₂` with `B x y ≠ 0`.-/
def separating_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
∀ x : M₁, (∀ y : M₂, B x y = 0) → x = 0

variables (M₁ M₂ I₁ I₂)

/-- In a non-trivial module, zero is not non-degenerate. -/
lemma not_separating_left_zero [nontrivial M₁] : ¬(0 : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R).separating_left :=
let ⟨m, hm⟩ := exists_ne (0 : M₁) in λ h, hm (h m $ λ n, rfl)

variables {M₁ M₂ I₁ I₂}

lemma separating_left.ne_zero [nontrivial M₁] {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R}
  (h : B.separating_left) : B ≠ 0 :=
λ h0, not_separating_left_zero M₁ M₂ I₁ I₂ $ h0 ▸ h

section linear

variables [add_comm_monoid Mₗ₁] [add_comm_monoid Mₗ₂] [add_comm_monoid Mₗ₁'] [add_comm_monoid Mₗ₂']
variables [module R Mₗ₁] [module R Mₗ₂] [module R Mₗ₁'] [module R Mₗ₂']
variables {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] R} (e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂')

lemma separating_left.congr (h : B.separating_left) :
  (e₁.arrow_congr (e₂.arrow_congr (linear_equiv.refl R R)) B).separating_left :=
begin
  intros x hx,
  rw ←e₁.symm.map_eq_zero_iff,
  refine h (e₁.symm x) (λ y, _),
  specialize hx (e₂ y),
  simp only [linear_equiv.arrow_congr_apply, linear_equiv.symm_apply_apply,
    linear_equiv.map_eq_zero_iff] at hx,
  exact hx,
end

@[simp] lemma separating_left_congr_iff :
  (e₁.arrow_congr (e₂.arrow_congr (linear_equiv.refl R R)) B).separating_left ↔ B.separating_left :=
⟨λ h, begin
  convert h.congr e₁.symm e₂.symm,
  ext x y,
  simp,
end, separating_left.congr e₁ e₂⟩

end linear

/-- A bilinear form is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`.-/
def separating_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0

/-- A bilinear form is called non-degenerate if it is left-separating and right-separating. -/
def nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop := separating_left B ∧ separating_right B

@[simp] lemma flip_separating_right {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.flip.separating_right ↔ B.separating_left := ⟨λ hB x hy, hB x hy, λ hB x hy, hB x hy⟩

@[simp] lemma flip_separating_left {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.flip.separating_left ↔ separating_right B := by rw [←flip_separating_right, flip_flip]

@[simp] lemma flip_nondegenerate {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.flip.nondegenerate ↔ B.nondegenerate :=
iff.trans and.comm (and_congr flip_separating_right flip_separating_left)

lemma separating_left_iff_linear_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_left ↔ ∀ x : M₁, B x = 0 → x = 0 :=
begin
  split; intros h x hB,
  { let h' := h x,
    simp only [hB, zero_apply, eq_self_iff_true, forall_const] at h',
    exact h' },
  have h' : B x = 0 := by { ext, rw [zero_apply], exact hB _ },
  exact h x h',
end

lemma separating_right_iff_linear_flip_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_right ↔ ∀ y : M₂, B.flip y = 0 → y = 0 :=
by rw [←flip_separating_left, separating_left_iff_linear_nontrivial]

/-- A bilinear form is left-separating if and only if it has a trivial kernel. -/
theorem separating_left_iff_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_left ↔ B.ker = ⊥ :=
iff.trans separating_left_iff_linear_nontrivial linear_map.ker_eq_bot'.symm

/-- A bilinear form is right-separating if and only if its flip has a trivial kernel. -/
theorem separating_right_iff_flip_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_right ↔ B.flip.ker = ⊥ :=
by rw [←flip_separating_left, separating_left_iff_ker_eq_bot]

end comm_semiring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M]
  {I I' : R →+* R}

lemma is_refl.nondegenerate_of_separating_left {B : M →ₗ[R] M →ₗ[R] R}
  (hB : B.is_refl) (hB' : B.separating_left) : B.nondegenerate :=
begin
  refine ⟨hB', _⟩,
  rw [separating_right_iff_flip_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mp],
  rwa ←separating_left_iff_ker_eq_bot,
end

lemma is_refl.nondegenerate_of_separating_right {B : M →ₗ[R] M →ₗ[R] R}
  (hB : B.is_refl) (hB' : B.separating_right) : B.nondegenerate :=
begin
  refine ⟨_, hB'⟩,
  rw [separating_left_iff_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr],
  rwa ←separating_right_iff_flip_ker_eq_bot,
end

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `disjoint W (W.orthogonal_bilin B)`. -/
lemma nondegenerate_restrict_of_disjoint_orthogonal
  {B : M →ₗ[R] M →ₗ[R] R} (hB : B.is_refl)
  {W : submodule R M} (hW : disjoint W (W.orthogonal_bilin B)) :
  (B.dom_restrict₁₂ W W).nondegenerate :=
begin
  refine (hB.dom_restrict_refl W).nondegenerate_of_separating_left  _,
  rintro ⟨x, hx⟩ b₁,
  rw [submodule.mk_eq_zero, ← submodule.mem_bot R],
  refine hW.le_bot ⟨hx, λ y hy, _⟩,
  specialize b₁ ⟨y, hy⟩,
  simp_rw [dom_restrict₁₂_apply, submodule.coe_mk] at b₁,
  rw hB.ortho_comm,
  exact b₁,
end

/-- An orthogonal basis with respect to a left-separating bilinear form has no self-orthogonal
elements. -/
lemma is_Ortho.not_is_ortho_basis_self_of_separating_left [nontrivial R]
  {B : M →ₛₗ[I] M →ₛₗ[I'] R} {v : basis n R M} (h : B.is_Ortho v) (hB : B.separating_left)
  (i : n) : ¬B.is_ortho (v i) (v i) :=
begin
  intro ho,
  refine v.ne_zero i (hB (v i) $ λ m, _),
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m,
  rw [basis.repr_symm_apply, finsupp.total_apply, finsupp.sum, map_sum],
  apply finset.sum_eq_zero,
  rintros j -,
  rw map_smulₛₗ,
  convert mul_zero _ using 2,
  obtain rfl | hij := eq_or_ne i j,
  { exact ho },
  { exact h hij },
end

/-- An orthogonal basis with respect to a right-separating bilinear form has no self-orthogonal
elements. -/
lemma is_Ortho.not_is_ortho_basis_self_of_separating_right [nontrivial R]
  {B : M →ₛₗ[I] M →ₛₗ[I'] R} {v : basis n R M} (h : B.is_Ortho v) (hB : B.separating_right)
  (i : n) : ¬B.is_ortho (v i) (v i) :=
begin
  rw is_Ortho_flip at h,
  rw is_ortho_flip,
  exact h.not_is_ortho_basis_self_of_separating_left (flip_separating_left.mpr hB) i,
end

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is left-separating
if the basis has no elements which are self-orthogonal. -/
lemma is_Ortho.separating_left_of_not_is_ortho_basis_self [no_zero_divisors R]
  {B : M →ₗ[R] M →ₗ[R] R} (v : basis n R M) (hO : B.is_Ortho v) (h : ∀ i, ¬B.is_ortho (v i) (v i)) :
  B.separating_left :=
begin
  intros m hB,
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m,
  rw linear_equiv.map_eq_zero_iff,
  ext i,
  rw [finsupp.zero_apply],
  specialize hB (v i),
  simp_rw [basis.repr_symm_apply, finsupp.total_apply, finsupp.sum, map_sum₂, map_smulₛₗ₂,
    smul_eq_mul] at hB,
  rw finset.sum_eq_single i at hB,
  { exact eq_zero_of_ne_zero_of_mul_right_eq_zero (h i) hB, },
  { intros j hj hij, convert mul_zero _ using 2, exact hO hij, },
  { intros hi, convert zero_mul _ using 2, exact finsupp.not_mem_support_iff.mp hi }
end

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is right-separating
if the basis has no elements which are self-orthogonal. -/
lemma is_Ortho.separating_right_iff_not_is_ortho_basis_self [no_zero_divisors R]
  {B : M →ₗ[R] M →ₗ[R] R} (v : basis n R M) (hO : B.is_Ortho v) (h : ∀ i, ¬B.is_ortho (v i) (v i)) :
  B.separating_right :=
begin
  rw is_Ortho_flip at hO,
  rw [←flip_separating_left],
  refine is_Ortho.separating_left_of_not_is_ortho_basis_self v hO (λ i, _),
  rw is_ortho_flip,
  exact h i,
end

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
if the basis has no elements which are self-orthogonal. -/
lemma is_Ortho.nondegenerate_of_not_is_ortho_basis_self [no_zero_divisors R]
  {B : M →ₗ[R] M →ₗ[R] R} (v : basis n R M) (hO : B.is_Ortho v) (h : ∀ i, ¬B.is_ortho (v i) (v i)) :
  B.nondegenerate :=
⟨is_Ortho.separating_left_of_not_is_ortho_basis_self v hO h,
  is_Ortho.separating_right_iff_not_is_ortho_basis_self v hO h⟩

end comm_ring

end nondegenerate

end linear_map
