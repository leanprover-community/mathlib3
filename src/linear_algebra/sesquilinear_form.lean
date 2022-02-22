/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import algebra.module.linear_map
import linear_algebra.bilinear_map
import linear_algebra.matrix.basis
import linear_algebra.dual

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

variables {R R₁ R₂ R₃ M M₁ M₂ K K₁ K₂ V V₁ V₂ n: Type*}

namespace linear_map

/-! ### Orthogonal vectors -/

section comm_ring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables [comm_semiring R] [comm_semiring R₁] [add_comm_monoid M₁] [module R₁ M₁]
  [comm_semiring R₂] [add_comm_monoid M₂] [module R₂ M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x y) : Prop := B x y = 0

lemma is_ortho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} {x y} :
  B.is_ortho x y ↔ B x y = 0 := iff.rfl

lemma is_ortho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : is_ortho B (0 : M₁) x :=
  by { dunfold is_ortho, rw [ map_zero B, zero_apply] }

lemma is_ortho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) (x) : is_ortho B x (0 : M₂) :=
  map_zero (B x)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def is_Ortho {n : Type*} (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R) (v : n → M₁) : Prop :=
pairwise (B.is_ortho on v)

lemma is_Ortho_def {n : Type*} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] R} {v : n → M₁} :
  B.is_Ortho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 := iff.rfl

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
    { rw I₁.map_eq_zero at H, trivial },
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
  apply I₁.map_eq_zero.mp,
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
begin
  intros x y,
  simp_rw dom_restrict₁₂_apply,
  exact H x y,
end

end is_symm

lemma is_symm_iff_flip {B : M →ₗ[R] M →ₗ[R] R} : B.is_symm ↔ B = B.flip :=
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

lemma is_alt_iff_flip_neg  [no_zero_divisors R] [char_zero R] (B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] R) :
  B.is_alt ↔ -B = B.flip :=
begin
  split; intro h,
  { ext,
    rw [neg_apply, flip_apply],
    exact h.neg _ _ },
  intros x,
  let h' := congr_fun₂ h x x,
  simp only [neg_apply, flip_apply, ←add_eq_zero_iff_neg_eq] at h',
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
{ inf_le_bot := eq_bot_iff.1 $
    (span_singleton_inf_orthogonal_eq_bot B x hx),
  top_le_sup := eq_top_iff.1 $ span_singleton_sup_orthogonal_eq_top hx }

end orthogonal

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

/-- A bilinear form is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`.-/
def separating_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop :=
∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0

/-- A bilinear form is called non-degenerate if it is left-separating and right-separating. -/
def nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R) : Prop := separating_left B ∧ separating_right B


variables (v : module.dual R₁ M₁) (x : M₁)
def dual_pairing : M₁ →ₗ[R₁] module.dual R₁ M₁ → R₁ :=
#check M₁ →[R] module.dual R₁ M₁

lemma separating_left_flip {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_left ↔ B.flip.separating_right := ⟨λ hB x hy, hB x hy, λ hB x hy, hB x hy⟩

lemma separating_right_flip {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  separating_right B ↔ B.flip.separating_left := by rw [separating_left_flip, flip_flip]

lemma separating_left_iff_neq_zero {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_left ↔ ∀ x : M₁, B x = 0 → x = 0 :=
begin
  split; intros h x hB,
  { let h' := h x,
    simp only [hB, zero_apply, eq_self_iff_true, forall_const] at h',
    exact h' },
  have h' : B x = 0 := by { ext, rw [zero_apply], exact hB _ },
  exact h x h',
end

lemma separating_right_iff_neq_zero_flip {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_right ↔ ∀ y : M₂, B.flip y = 0 → y = 0 :=
by rw [separating_right_flip, separating_left_iff_neq_zero]

/-- A bilinear form is left-separating if and only if it has a trivial kernel. -/
theorem separating_left_iff_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_left ↔ B.ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot',
  split; intro h,
  { refine λ m hm, h _ (λ x, _),
    rw hm, refl },
  { intros m hm, apply h,
    ext x, exact hm x }
end

/-- A bilinear form is right-separating if and only if its flip has a trivial kernel. -/
theorem separating_right_iff_flip_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] R} :
  B.separating_right ↔ B.flip.ker = ⊥ :=
by rw [separating_right_flip, separating_left_iff_ker_eq_bot]

end comm_semiring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M]
  {I : R →+* R}

lemma nondegenerate_of_symm_separating_left {B : M →ₗ[R] M →ₗ[R] R}
  (hB : B.is_symm) (hB' : B.separating_left) : B.nondegenerate :=
begin
  refine ⟨hB', _⟩,
  rw [is_symm_iff_flip.mp hB, ←separating_left_flip],
  exact hB',
end

/-- The restriction of a symmetric bilinear form `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `disjoint W (W.orthogonal_bilin B)`. -/
lemma nondegenerate_restrict_of_disjoint_orthogonal
  {B : M →ₗ[R] M →ₗ[R] R} (hB : B.is_symm)
  {W : submodule R M} (hW : disjoint W (W.orthogonal_bilin B)) :
  (B.dom_restrict₁₂ W W).nondegenerate :=
begin
  refine nondegenerate_of_symm_separating_left (hB.dom_restrict_symm W) _,
  rintro ⟨x, hx⟩ b₁,
  rw [submodule.mk_eq_zero, ← submodule.mem_bot R],
  refine hW ⟨hx, λ y hy, _⟩,
  specialize b₁ ⟨y, hy⟩,
  simp_rw [dom_restrict₁₂_apply, submodule.coe_mk] at b₁,
  rw hB.ortho_comm,
  exact b₁,
end

end comm_ring



end nondegenerate

section to_matrix

variables [comm_ring R] [add_comm_group M] [module R M]
variables [decidable_eq n] (b : basis n R M)

/-- This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
noncomputable def bilin_form_to_matrix_aux2 (b : basis n R M) : (M →ₗ[R] M →ₗ[R] R) →ₗ[R] matrix n n R :=
{ to_fun := λ B i j, B (b i) (b j),
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl }


end to_matrix

end linear_map
