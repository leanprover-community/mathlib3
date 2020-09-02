-- this should all be moved

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import data.finset.lattice
import data.set.disjointed
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic

universes u v w u₁

-- ### FOR_MATHLIB



namespace mv_polynomial
open finsupp

variables (σ R A : Type*) [comm_semiring R] [comm_semiring A]


section constant_coeff
open_locale classical
variables {σ R}

end constant_coeff

open_locale big_operators

lemma C_dvd_iff_dvd_coeff {σ : Type*} {R : Type*} [comm_ring R]
  (r : R) (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ ∀ i, r ∣ (φ.coeff i) :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : (σ →₀ ℕ) → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : mv_polynomial σ R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    apply mv_polynomial.ext, intro i,
    simp only [coeff_C_mul, coeff_sum, coeff_monomial],
    rw [finset.sum_eq_single i, if_pos rfl],
    { dsimp [c'], split_ifs with hi hi,
      { rw hc },
      { rw finsupp.not_mem_support_iff at hi, rwa [mul_zero] } },
    { intros j hj hji, convert if_neg hji },
    { intro hi, rw [if_pos rfl], exact if_neg hi } }
end

-- Johan: why the hack does ring_hom.ker not exist!!!
-- Rob: it does now, why do you ask here?

lemma C_dvd_iff_map_hom_eq_zero {σ : Type*} {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]
  (q : R →+* S) (hq : function.surjective q) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
  (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ map q φ = 0 :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intro h, apply mv_polynomial.ext, intro i,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero], },
  { rw mv_polynomial.ext_iff,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero, imp_self] }
end

lemma C_dvd_iff_zmod {σ : Type*} (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
begin
  apply C_dvd_iff_map_hom_eq_zero,
  { exact zmod.int_cast_surjective },
  { exact char_p.int_cast_eq_zero_iff (zmod n) n, }
end

end mv_polynomial

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R S : Type*} [comm_semiring R] [comm_semiring S]
variables (f : R →+* S)
variables (p q : mv_polynomial σ R)

open function
open_locale classical big_operators

section vars

end vars

end mv_polynomial


namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [comm_semiring R]

/-- This is an example of a map of “algebraic varieties for dummies” over `R`.
(Not meant in a degrading way. Just that we don'y have any actual varieties in Lean yet.) -/
noncomputable def comap (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) :
  (τ → R) → (σ → R) :=
λ x i, aeval x (f (X i))

@[simp] lemma comap_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) (x : τ → R) (i : σ) :
  comap f x i = aeval x (f (X i)) := rfl

@[simp] lemma comap_id_apply (x : σ → R) : comap (alg_hom.id R (mv_polynomial σ R)) x = x :=
by { funext i, simp only [comap, alg_hom.id_apply, id.def, aeval_X], }

variables (σ R)

lemma comap_id : comap (alg_hom.id R (mv_polynomial σ R)) = id :=
by { funext x, exact comap_id_apply x }

variables {σ R}

lemma comap_comp_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) x = (comap f) (comap g x) :=
begin
  funext i,
  transitivity (aeval x (aeval (λ i, g (X i)) (f (X i)))),
  { apply eval₂_hom_congr rfl rfl,
    rw alg_hom.comp_apply,
    suffices : g = aeval (λ i, g (X i)), { rw ← this, },
    apply mv_polynomial.alg_hom_ext g,
    intro, rw [aeval_X], },
  { simp only [comap, aeval_eq_eval₂_hom, map_eval₂_hom, alg_hom.comp_apply],
    refine eval₂_hom_congr _ rfl rfl,
    ext r, apply aeval_C },
end

lemma comap_comp (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) = (comap f) ∘ (comap g) :=
by { funext x, exact comap_comp_apply _ _ _ }

lemma comap_eq_id_of_eq_id (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R)
  (hf : ∀ φ, f φ = φ) (x : σ → R) :
  comap f x = x :=
by { convert comap_id_apply x, ext1 φ, rw [hf, alg_hom.id_apply] }

noncomputable def comap_equiv (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (τ → R) ≃ (σ → R) :=
{ to_fun    := comap f,
  inv_fun   := comap f.symm,
  left_inv  := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
    simp only [alg_hom.id_apply, alg_equiv.comp_symm], },
  right_inv := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
  simp only [alg_hom.id_apply, alg_equiv.symm_comp] }, }

@[simp] lemma comap_equiv_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (comap_equiv f : (τ → R) → (σ → R)) = comap f := rfl

@[simp] lemma comap_equiv_symm_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  ((comap_equiv f).symm : (σ → R) → (τ → R)) = comap f.symm := rfl

lemma equiv_of_family_aux (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (h : ∀ i, aeval g (f i) = X i) (φ : mv_polynomial σ R) :
  (aeval g) (aeval f φ) = φ :=
begin
  rw ← alg_hom.comp_apply,
  suffices : (aeval g).comp (aeval f) = alg_hom.id _ _,
  { rw [this, alg_hom.id_apply], },
  refine mv_polynomial.alg_hom_ext _ (alg_hom.id _ _) _,
  intro i,
  rw [alg_hom.comp_apply, alg_hom.id_apply, aeval_X, h],
end

noncomputable def equiv_of_family (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
{ to_fun    := aeval f,
  inv_fun   := aeval g,
  left_inv  := equiv_of_family_aux f g hfg,
  right_inv := equiv_of_family_aux g f hgf,
  .. aeval f}

@[simp] lemma equiv_of_family_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  (equiv_of_family f g hfg hgf : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) = aeval f := rfl

@[simp] lemma equiv_of_family_symm_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  ((equiv_of_family f g hfg hgf).symm : mv_polynomial τ R →ₐ[R] mv_polynomial σ R) = aeval g := rfl

@[simp] lemma equiv_of_family_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial σ R) :
  equiv_of_family f g hfg hgf φ = aeval f φ := rfl

@[simp] lemma equiv_of_family_symm_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial τ R) :
  (equiv_of_family f g hfg hgf).symm φ = aeval g φ := rfl

-- I think this stuff should move back to the witt_vector file
namespace witt_structure_machine
variable {idx : Type*}
variables (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
variables (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)

noncomputable def structure_polynomial (Φ : mv_polynomial idx R) (t : τ) :
  mv_polynomial (idx × τ) R :=
aeval (λ s : σ, (aeval (λ i, (rename (λ t', (i,t')) (f s)))) Φ) (g t)

include hfg

theorem structure_polynomial_prop (Φ : mv_polynomial idx R) (s : σ) :
  aeval (structure_polynomial f g Φ) (f s) = aeval (λ b, (rename (λ i, (b,i)) (f s))) Φ :=
calc aeval (structure_polynomial f g Φ) (f s) =
      aeval (λ s', aeval (λ b, (rename (prod.mk b)) (f s')) Φ) (aeval g (f s)) :
      by { conv_rhs { rw [aeval_eq_eval₂_hom, map_aeval] },
           apply eval₂_hom_congr _ rfl rfl,
           ext1 r, symmetry, apply eval₂_hom_C, }
... = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ : by rw [hfg, aeval_X]

include hgf

theorem exists_unique (Φ : mv_polynomial idx R) :
  ∃! (φ : τ → mv_polynomial (idx × τ) R),
    ∀ (s : σ), aeval φ (f s) = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ :=
begin
  refine ⟨structure_polynomial f g Φ, structure_polynomial_prop _ _ hfg _, _⟩,
  { intros φ H,
    funext t,
    calc φ t = aeval φ (aeval (f) (g t))    : by rw [hgf, aeval_X]
         ... = structure_polynomial f g Φ t : _,
    rw [aeval_eq_eval₂_hom, map_aeval],
    apply eval₂_hom_congr _ _ rfl,
    { ext1 r, exact eval₂_C _ _ r, },
    { funext k, exact H k } }
end

end witt_structure_machine

section monadic_stuff
variables {S T : Type*} [comm_semiring S] [comm_semiring T]

noncomputable def bind₁ (f : σ → mv_polynomial τ R) : mv_polynomial σ R →ₐ[R] mv_polynomial τ R :=
aeval f

noncomputable def bind₂ (f : R →+* mv_polynomial σ S) : mv_polynomial σ R →+* mv_polynomial σ S :=
eval₂_hom f X

noncomputable def join₁ : mv_polynomial (mv_polynomial σ R) R →ₐ[R] mv_polynomial σ R :=
aeval (ring_hom.id _)

noncomputable def join₂ : mv_polynomial σ (mv_polynomial σ R) →+* mv_polynomial σ R :=
eval₂_hom (ring_hom.id _) X

@[simp] lemma aeval_X_left (φ : mv_polynomial σ R) : aeval X φ = φ :=
begin
  apply φ.induction_on,
  { intro, rw aeval_C, refl },
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add] },
  { intros p n hp, simp only [hp, aeval_X, alg_hom.map_mul] }
end

@[simp]
lemma bind₁_X_left : bind₁ (X : σ → mv_polynomial σ R) = alg_hom.id R _ :=
by ext1; simp [bind₁]

@[simp]
lemma bind₁_X_right (f : σ → mv_polynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
aeval_X f i

variable (f : σ → mv_polynomial τ R)
variable x : R

@[simp]
lemma bind₁_C_right (f : σ → mv_polynomial τ R) (x) : bind₁ f (C x) = C x :=
by simp [bind₁, C, aeval_monomial, finsupp.prod_zero_index]; refl

@[simp]
lemma bind₂_C_left : bind₂ (C : R →+* mv_polynomial σ R) = ring_hom.id _ :=
by ext1; simp [bind₂]

@[simp]
lemma bind₂_C_right (f : R →+* mv_polynomial σ S) (r : R) : bind₂ f (C r) = f r :=
eval₂_hom_C f X r

@[simp]
lemma bind₂_comp_C (f : R →+* mv_polynomial σ S) :
  (bind₂ f).comp C = f :=
by { ext1, apply bind₂_C_right }

@[simp]
lemma join₂_map (f : R →+* mv_polynomial σ S) (φ : mv_polynomial σ R) :
  join₂ (map f φ) = bind₂ f φ :=
by simp only [join₂, bind₂, eval₂_hom_map_hom, ring_hom.id_comp]

@[simp]
lemma join₂_comp_map (f : R →+* mv_polynomial σ S) :
  join₂.comp (map f) = bind₂ f :=
by ext1; simp [join₂, bind₂]

-- TODO: upgrade `rename` to an `R`-algebra hom,
-- and mention that it is `map` in first argument of `mv_polynomial`.

@[simp] lemma aeval_rename (f : σ → mv_polynomial τ R) (p : mv_polynomial σ R) :
  aeval (ring_hom.id (mv_polynomial τ R)) (rename f p) = aeval f p :=
begin
  apply p.induction_on,
  { simp only [aeval_C, forall_const, eq_self_iff_true, rename_C]},
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add, ring_hom.map_add] },
  { intros p n hp, simp only [hp, rename_X, ring_hom.id_apply, aeval_X, ring_hom.map_mul, alg_hom.map_mul]}
end

@[simp]
lemma join₁_rename (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  join₁ (rename f φ) = bind₁ f φ :=
by simp [join₁, bind₁]

@[simp]
lemma bind₁_id : bind₁ (@id (mv_polynomial σ R)) = join₁ := rfl

@[simp]
lemma bind₂_id : bind₂ (ring_hom.id (mv_polynomial σ R)) = join₂ := rfl

lemma bind₁_bind₁ (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R) (φ : mv_polynomial σ R) :
  (bind₁ g) (bind₁ f φ) = bind₁ (λ i, bind₁ g (f i)) φ :=
by simp [bind₁, ← comp_aeval]

lemma bind₁_comp_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial υ R) :
  (bind₁ g).comp (bind₁ f) = bind₁ (λ i, bind₁ g (f i)) :=
by { ext1, apply bind₁_bind₁ }

lemma bind₂_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T) (φ : mv_polynomial σ R) :
  (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
begin
  dsimp [bind₂],
  apply φ.induction_on,
  { simp },
  { intros p q hp hq, simp only [hp, hq, eval₂_add] },
  { intros p n hp, simp only [hp, eval₂_mul, eval₂_X] }
end

lemma bind₂_comp_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* mv_polynomial σ T) :
  (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) :=
by { ext1, simp only [function.comp_app, ring_hom.coe_comp, bind₂_bind₂], }

lemma rename_bind₁ {υ : Type*} (f : σ → mv_polynomial τ R) (g : τ → υ) (φ : mv_polynomial σ R) :
  rename g (bind₁ f φ) = bind₁ (λ i, rename g $ f i) φ :=
begin
  apply φ.induction_on,
  { intro a, simp },
  { intros p q hp hq, simp [hp, hq] },
  { intros p n hp, simp [hp] }
end

lemma map_bind₂ (f : R →+* mv_polynomial σ S) (g : S →+* T) (φ : mv_polynomial σ R) :
  map g (bind₂ f φ) = bind₂ ((map g).comp f) φ :=
begin
  simp only [bind₂, eval₂_comp_right, coe_eval₂_hom, eval₂_map],
  congr' 1 with : 1,
  simp only [function.comp_app, map_X]
end

lemma bind₁_rename {υ : Type*} (f : τ → mv_polynomial υ R) (g : σ → τ) (φ : mv_polynomial σ R) :
  bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
begin
  dsimp [bind₁],
  apply φ.induction_on,
  { simp },
  { intros p q hp hq, simp only [hp, hq, alg_hom.map_add, ring_hom.map_add]},
  { intros p n hp, simp only [hp, rename_X, aeval_X, ring_hom.map_mul, alg_hom.map_mul] }
end

lemma bind₂_map (f : S →+* mv_polynomial σ T) (g : R →+* S) (φ : mv_polynomial σ R) :
  bind₂ f (map g φ) = bind₂ (f.comp g) φ :=
by simp [bind₂]

@[simp]
lemma map_comp_C (f : R →+* S) : (map f).comp (C : R →+* mv_polynomial σ R) = C.comp f :=
by { ext1, apply map_C }

-- mixing the two monad structures
lemma hom_bind₁ (f : mv_polynomial τ R →+* S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  f (bind₁ g φ) = eval₂_hom (f.comp C) (λ i, f (g i)) φ :=
by rw [bind₁, map_aeval, algebra_map_eq]

lemma map_bind₁ (f : R →+* S) (g : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  map f (bind₁ g φ) = bind₁ (λ (i : σ), (map f) (g i)) (map f φ) := -- eval₂_hom (C.comp f) (λ i, map f (g i)) φ :=
by { rw [hom_bind₁, map_comp_C, ← eval₂_hom_map_hom], refl }

@[simp]
lemma eval₂_hom_C_left (f : σ → mv_polynomial τ R) : eval₂_hom C f = bind₁ f := rfl


section

open_locale classical
variables (φ : mv_polynomial σ R)

-- -- jmc: I don't know what the correct statement is here...
-- lemma bind₁_support : (bind₁ f φ).support ⊆ _ :=
-- begin
-- end

-- lemma finset.not_subset {α} {s t : finset α} : ¬ s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t :=
-- sorry
-- variables (p q : mv_polynomial σ R)
-- #simp bind₁ f (p + q)


-- I've made a few starts at this, none of them feel right.
-- this might not be the right lemma
-- but it proves bind₁_vars
lemma foo
  (a : τ →₀ ℕ)
   :
  coeff a ((aeval f) φ) ≠ 0 → ∃ s : σ, s ∈ φ.vars ∧ a ∈ (f s).support  :=
begin
  simp only [aeval, eval₂_eq, ring_hom.to_fun_eq_coe, coe_eval₂_hom, finsupp.mem_support_iff, ne.def, alg_hom.coe_mk],
  contrapose!, intro h,
  simp only [coeff_sum],
  apply finset.sum_eq_zero,
  intros x hx,
  simp only [mem_vars] at h,
  convert h _ _,


  -- by_cases xz : x = 0,
  -- { simp [xz], admit },
  -- { obtain ⟨c, hc⟩ : ∃ c, c ∈ x.support := sorry,
  --   have := h c ⟨x, hx, hc⟩,
  -- convert coeff_zero _,
  -- convert mul_zero _,
  -- apply finset.prod_eq_zero,
  -- { exact hc },
  -- { convert zero_pow' _ _,
  --   {  },
  --   { simpa using hc }   }
  --  }

  -- simp only [aeval, eval₂_eq, ring_hom.to_fun_eq_coe, coe_eval₂_hom, finsupp.mem_support_iff, ne.def, alg_hom.coe_mk],
  -- contrapose!, intro h,
  -- simp only [coeff_sum],
  -- apply finset.sum_eq_zero,
  -- intros x hx,
  -- convert coeff_zero _,
  -- convert mul_zero _,
  -- apply finset.prod_eq_zero,

end

lemma bind₁_vars : (bind₁ f φ).vars ⊆ φ.vars.bind (λ i, (f i).vars) :=
begin

  intro x,
  simp [vars, ← finset.bind_to_finset, bind₁],
  intro hx,
  obtain ⟨a, ha, hax⟩ := mem_degrees.mp hx,
  -- rw coeff_aeval at ha,
  rcases foo _ _ _ ha with ⟨s, hs, hs2⟩,
  simp [vars] at hs,
  use [s, hs],
  rw degrees,
  rw finset.mem_sup,
  use [a, hs2],
  rw finsupp.mem_to_multiset, exact hax
  -- rw aeval_coe
  -- apply φ.induction_on,
  -- { intro a, simp },
  -- { intros p q hp hq,
  --   simp,
  --   apply finset.subset.trans (vars_add_subset _ _),
  --   apply finset.union_subset,
  --   sorry, sorry },
  -- { intros p n hp, simp [hp], }
end

end

end monadic_stuff

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
-- this definition should also work for non-commutative `R`
noncomputable def expand (p : ℕ) : mv_polynomial σ R →ₐ[R] mv_polynomial σ R :=
{ commutes' := λ r, eval₂_hom_C _ _ _,
  .. (eval₂_hom C (λ i, (X i) ^ p) : mv_polynomial σ R →+* mv_polynomial σ R) }

@[simp] lemma expand_C (p : ℕ) (r : R) : expand p (C r : mv_polynomial σ R) = C r :=
eval₂_hom_C _ _ _

@[simp] lemma expand_X (p : ℕ) (i : σ) : expand p (X i : mv_polynomial σ R) = (X i) ^ p :=
eval₂_hom_X' _ _ _

lemma expand_comp_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) :
  (expand p).comp (bind₁ f) = bind₁ (λ i, expand p (f i)) :=
by { apply alg_hom_ext, intro i, simp only [alg_hom.comp_apply, bind₁_X_right], }

lemma expand_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  expand p (bind₁ f φ) = bind₁ (λ i, expand p (f i)) φ :=
by rw [← alg_hom.comp_apply, expand_comp_bind₁]

section
variables {S : Type*} [comm_semiring S]

lemma map_expand (f : R →+* S) (p : ℕ) (φ : mv_polynomial σ R) :
  map f (expand p φ) = expand p (map f φ) :=
begin
  sorry
end

-- TODO: prove `rename_comp_expand`

lemma rename_expand (f : σ → τ) (p : ℕ) (φ : mv_polynomial σ R) :
  rename f (expand p φ) = expand p (rename f φ) :=
begin
  sorry
end

end

end mv_polynomial

-- ### end FOR_MATHLIB
