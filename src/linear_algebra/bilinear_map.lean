/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/

import linear_algebra.basic
import linear_algebra.basis

/-!
# Basics on bilinear maps

This file provides basics on bilinear maps. The most general form considered are maps that are
semilinear in both arguments. They are of type `M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P`, where `M` and `N`
are modules over `R` and `S` respectively, `P` is a module over both `R₂` and `S₂` with
commuting actions, and `ρ₁₂ : R →+* R₂` and `σ₁₂ : S →+* S₂`.

## Main declarations

* `linear_map.mk₂`: a constructor for bilinear maps,
  taking an unbundled function together with proof witnesses of bilinearity
* `linear_map.flip`: turns a bilinear map `M × N → P` into `N × M → P`
* `linear_map.lcomp` and `linear_map.llcomp`: composition of linear maps as a bilinear map
* `linear_map.compl₂`: composition of a bilinear map `M × N → P` with a linear map `Q → M`
* `linear_map.compr₂`: composition of a bilinear map `M × N → P` with a linear map `Q → N`
* `linear_map.lsmul`: scalar multiplication as a bilinear map `R × M → M`

## Tags

bilinear
-/

variables {ι₁ ι₂ : Type*}

namespace linear_map

section semiring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables {R : Type*} [semiring R] {S : Type*} [semiring S]
variables {R₂ : Type*} [semiring R₂] {S₂ : Type*} [semiring S₂]
variables {M : Type*} {N : Type*} {P : Type*}
variables {M₂ : Type*} {N₂ : Type*} {P₂ : Type*}
variables {Nₗ : Type*} {Pₗ : Type*}
variables {M' : Type*} {N' : Type*} {P' : Type*}

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
variables [add_comm_monoid M₂] [add_comm_monoid N₂] [add_comm_monoid P₂]
variables [add_comm_monoid Nₗ] [add_comm_monoid Pₗ]
variables [add_comm_group M'] [add_comm_group N'] [add_comm_group P']
variables [module R M] [module S N] [module R₂ P] [module S₂ P]
variables [module R M₂] [module S N₂] [module R P₂] [module S₂ P₂]
variables [module R Pₗ] [module S Pₗ]
variables [module R M'] [module S N'] [module R₂ P'] [module S₂ P']
variables [smul_comm_class S₂ R₂ P] [smul_comm_class S R Pₗ] [smul_comm_class S₂ R₂ P']
variables [smul_comm_class S₂ R P₂]
variables {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variables (ρ₁₂ σ₁₂)
/-- Create a bilinear map from a function that is semilinear in each component.
See `mk₂'` and `mk₂` for the linear case. -/
def mk₂'ₛₗ (f : M → N → P)
  (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (H2 : ∀ (c:R) m n, f (c • m) n = (ρ₁₂ c) • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (H4 : ∀ (c:S) m n, f m (c • n) = (σ₁₂ c) • f m n) : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P :=
{ to_fun := λ m, { to_fun := f m, map_add' := H3 m, map_smul' := λ c, H4 c m},
  map_add' := λ m₁ m₂, linear_map.ext $ H1 m₁ m₂,
  map_smul' := λ c m, linear_map.ext $ H2 c m }
variables {ρ₁₂ σ₁₂}

@[simp] theorem mk₂'ₛₗ_apply
  (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂'ₛₗ ρ₁₂ σ₁₂ f H1 H2 H3 H4 : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) m n = f m n := rfl

variables (R S)
/-- Create a bilinear map from a function that is linear in each component.
See `mk₂` for the special case where both arguments come from modules over the same ring. -/
def mk₂' (f : M → N → Pₗ)
  (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (H2 : ∀ (c:R) m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (H4 : ∀ (c:S) m n, f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[S] Pₗ :=
mk₂'ₛₗ (ring_hom.id R) (ring_hom.id S) f H1 H2 H3 H4
variables {R S}

@[simp] theorem mk₂'_apply
  (f : M → N → Pₗ) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂' R S f H1 H2 H3 H4 : M →ₗ[R] N →ₗ[S] Pₗ) m n = f m n := rfl

theorem ext₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P}
  (H : ∀ m n, f m n = g m n) : f = g :=
linear_map.ext (λ m, linear_map.ext $ λ n, H m n)

lemma congr_fun₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : f = g) (x y) : f x y = g x y :=
linear_map.congr_fun (linear_map.congr_fun h x) y

section

local attribute [instance] smul_comm_class.symm

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=
mk₂'ₛₗ σ₁₂ ρ₁₂ (λ n m, f m n)
  (λ n₁ n₂ m, (f m).map_add _ _)
  (λ c n m, (f m).map_smulₛₗ _ _)
  (λ n m₁ m₂, by rw f.map_add; refl)
  (λ c n m, by rw f.map_smulₛₗ; refl)

end

@[simp] theorem flip_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n := rfl

@[simp] lemma flip_flip [smul_comm_class R₂ S₂ P] (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) :
  f.flip.flip = f := linear_map.ext₂ (λ x y, ((f.flip).flip_apply _ _).trans (f.flip_apply _ _))

open_locale big_operators

variables {R}
theorem flip_inj {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : flip f = flip g) : f = g :=
ext₂ $ λ m n, show flip f n m = flip g n m, by rw H

theorem map_zero₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (y) : f 0 y = 0 :=
(flip f y).map_zero

theorem map_neg₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y) : f (-x) y = -f x y :=
(flip f y).map_neg _

theorem map_sub₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y z) : f (x - y) z = f x z - f y z :=
(flip f z).map_sub _ _

theorem map_add₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y :=
(flip f y).map_add _ _

theorem map_smul₂ (f : M₂ →ₗ[R] N₂ →ₛₗ[σ₁₂] P₂) (r : R) (x y) : f (r • x) y = r • f x y :=
(flip f y).map_smul _ _

theorem map_smulₛₗ₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (r : R) (x y) : f (r • x) y = (ρ₁₂ r) • f x y :=
(flip f y).map_smulₛₗ _ _

theorem map_sum₂ {ι : Type*} (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (t : finset ι) (x : ι → M) (y) :
  f (∑ i in t, x i) y = ∑ i in t, f (x i) y :=
(flip f y).map_sum

/-- Restricting a bilinear map in the second entry -/
def dom_restrict₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : submodule S N) :
  M →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P :=
{ to_fun := λ m, (f m).dom_restrict q,
  map_add' := λ m₁ m₂, linear_map.ext $ λ _, by simp only [map_add, dom_restrict_apply, add_apply],
  map_smul' := λ c m, linear_map.ext $ λ _, by simp only [f.map_smulₛₗ, dom_restrict_apply,
    smul_apply]}

lemma dom_restrict₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : submodule S N) (x : M) (y : q) :
  f.dom_restrict₂ q x y = f x y := rfl

/-- Restricting a bilinear map in both components -/
def dom_restrict₁₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : submodule R M) (q : submodule S N) :
  p →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P := (f.dom_restrict p).dom_restrict₂ q

lemma dom_restrict₁₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : submodule R M) (q : submodule S N)
  (x : p) (y : q) : f.dom_restrict₁₂ p q x y = f x y := rfl

end semiring

section comm_semiring

variables {R : Type*} [comm_semiring R] {R₂ : Type*} [comm_semiring R₂]
variables {R₃ : Type*} [comm_semiring R₃] {R₄ : Type*} [comm_semiring R₄]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variables {Mₗ : Type*} {Nₗ : Type*} {Pₗ : Type*} {Qₗ Qₗ': Type*}

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
variables [add_comm_monoid Mₗ] [add_comm_monoid Nₗ] [add_comm_monoid Pₗ]
variables [add_comm_monoid Qₗ] [add_comm_monoid Qₗ']
variables [module R M] [module R₂ N] [module R₃ P] [module R₄ Q]
variables [module R Mₗ] [module R Nₗ] [module R Pₗ] [module R Qₗ] [module R Qₗ']
variables {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variables {σ₄₂ : R₄ →+* R₂} {σ₄₃ : R₄ →+* R₃}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₄₂ σ₂₃ σ₄₃]

variables (R)

/-- Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`. -/
def mk₂ (f : M → Nₗ → Pₗ)
  (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (H2 : ∀ (c:R) m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (H4 : ∀ (c:R) m n, f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=
mk₂' R R f H1 H2 H3 H4

@[simp] theorem mk₂_apply
  (f : M → Nₗ → Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ) :
  (mk₂ R f H1 H2 H3 H4 : M →ₗ[R] Nₗ →ₗ[R] Pₗ) m n = f m n := rfl

variables (R M N P)
/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map `M → N → P`,
change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def lflip : (M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) →ₗ[R₃] N →ₛₗ[σ₂₃] M →ₛₗ[σ₁₃] P :=
{ to_fun := flip, map_add' := λ _ _, rfl, map_smul' := λ _ _, rfl }
variables {R M N P}

variables (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P)

@[simp] theorem lflip_apply (m : M) (n : N) : lflip R M N P f n m = f m n := rfl

variables (R Pₗ)
/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def lcomp (f : M →ₗ[R] Nₗ) : (Nₗ →ₗ[R] Pₗ) →ₗ[R] M →ₗ[R] Pₗ :=
flip $ linear_map.comp (flip id) f

variables {R Pₗ}

@[simp] theorem lcomp_apply (f : M →ₗ[R] Nₗ) (g : Nₗ →ₗ[R] Pₗ) (x : M) :
  lcomp R Pₗ f g x = g (f x) := rfl

theorem lcomp_apply' (f : M →ₗ[R] Nₗ) (g : Nₗ →ₗ[R] Pₗ) :
  lcomp R Pₗ f g = g ∘ₗ f := rfl

variables (P σ₂₃)
/-- Composing a semilinear map `M → N` and a semilinear map `N → P` to form a semilinear map
`M → P` is itself a linear map. -/
def lcompₛₗ (f : M →ₛₗ[σ₁₂] N) : (N →ₛₗ[σ₂₃] P) →ₗ[R₃] M →ₛₗ[σ₁₃] P :=
flip $ linear_map.comp (flip id) f
variables {P σ₂₃}

include σ₁₃
@[simp] theorem lcompₛₗ_apply (f : M →ₛₗ[σ₁₂] N) (g : N →ₛₗ[σ₂₃] P) (x : M) :
  lcompₛₗ P σ₂₃ f g x = g (f x) := rfl
omit σ₁₃

variables (R M Nₗ Pₗ)
/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def llcomp : (Nₗ →ₗ[R] Pₗ) →ₗ[R] (M →ₗ[R] Nₗ) →ₗ[R] M →ₗ[R] Pₗ :=
flip { to_fun := lcomp R Pₗ,
       map_add' := λ f f', ext₂ $ λ g x, g.map_add _ _,
       map_smul' := λ (c : R) f, ext₂ $ λ g x, g.map_smul _ _ }
variables {R M Nₗ Pₗ}

section
@[simp] theorem llcomp_apply (f : Nₗ →ₗ[R] Pₗ) (g : M →ₗ[R] Nₗ) (x : M) :
  llcomp R M Nₗ Pₗ f g x = f (g x) := rfl

theorem llcomp_apply' (f : Nₗ →ₗ[R] Pₗ) (g : M →ₗ[R] Nₗ) :
  llcomp R M Nₗ Pₗ f g = f ∘ₗ g := rfl
end

/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
def compl₂ (g : Q →ₛₗ[σ₄₂] N) : M →ₛₗ[σ₁₃] Q →ₛₗ[σ₄₃] P := (lcompₛₗ _ _ g).comp f

include σ₄₃
@[simp] theorem compl₂_apply (g : Q →ₛₗ[σ₄₂] N) (m : M) (q : Q) :
  f.compl₂ g m q = f m (g q) := rfl
omit σ₄₃

/-- Composing linear maps `Q → M` and `Q' → N` with a bilinear map `M → N → P` to
form a bilinear map `Q → Q' → P`. -/
def compl₁₂ (f : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Qₗ →ₗ[R] Mₗ) (g' : Qₗ' →ₗ[R] Nₗ) :
  Qₗ →ₗ[R] Qₗ' →ₗ[R] Pₗ :=
(f.comp g).compl₂ g'

@[simp] theorem compl₁₂_apply (f : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Qₗ →ₗ[R] Mₗ) (g' : Qₗ' →ₗ[R] Nₗ)
  (x : Qₗ) (y : Qₗ') : f.compl₁₂ g g' x y = f (g x) (g' y) := rfl

lemma compl₁₂_inj {f₁ f₂ : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ} {g : Qₗ →ₗ[R] Mₗ} {g' : Qₗ' →ₗ[R] Nₗ}
  (hₗ : function.surjective g) (hᵣ : function.surjective g') :
  f₁.compl₁₂ g g' = f₂.compl₁₂ g g' ↔ f₁ = f₂ :=
begin
  split; intros h,
  { -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y,
    cases hₗ x with x' hx, subst hx,
    cases hᵣ y with y' hy, subst hy,
    convert linear_map.congr_fun₂ h x' y' },
  { -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h },
end

/-- Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`. -/
def compr₂ (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) : M →ₗ[R] Nₗ →ₗ[R] Qₗ :=
(llcomp R Nₗ Pₗ Qₗ g) ∘ₗ f

@[simp] theorem compr₂_apply (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) (m : M) (n : Nₗ) :
  f.compr₂ g m n = g (f m n) := rfl

variables (R M)
/-- Scalar multiplication as a bilinear map `R → M → M`. -/
def lsmul : R →ₗ[R] M →ₗ[R] M :=
mk₂ R (•) add_smul (λ _ _ _, mul_smul _ _ _) smul_add
(λ r s m, by simp only [smul_smul, smul_eq_mul, mul_comm])
variables {R M}

@[simp] theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m := rfl

end comm_semiring

section comm_ring

variables {R R₂ S S₂ M N P : Type*}
variables [comm_ring R] [comm_ring S] [comm_ring R₂] [comm_ring S₂]
variables [add_comm_group M] [add_comm_group N] [add_comm_group P]
variables [module R M] [module S N] [module R₂ P] [module S₂ P]
variables [smul_comm_class S₂ R₂ P]
variables {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
variables (b₁ : basis ι₁ R M) (b₂ : basis ι₂ S N)

lemma lsmul_injective [no_zero_smul_divisors R M] {x : R} (hx : x ≠ 0) :
  function.injective (lsmul R M x) :=
smul_right_injective _ hx

lemma ker_lsmul [no_zero_smul_divisors R M] {a : R} (ha : a ≠ 0) :
  (linear_map.lsmul R M a).ker = ⊥ :=
linear_map.ker_eq_bot_of_injective (linear_map.lsmul_injective ha)


/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
lemma ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P}
  (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) : B = B' :=
b₁.ext $ λ i, b₂.ext $ λ j, h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
lemma sum_repr_mul_repr_mul {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
  (b₁.repr x).sum (λ i xi, (b₂.repr y).sum (λ j yj, (ρ₁₂ xi) • (σ₁₂ yj) • B (b₁ i) (b₂ j))) =
  B x y :=
begin
  conv_rhs { rw [← b₁.total_repr x, ← b₂.total_repr y] },
  simp_rw [finsupp.total_apply, finsupp.sum, map_sum₂, map_sum,
    linear_map.map_smulₛₗ₂, linear_map.map_smulₛₗ],
end


end comm_ring

end linear_map
