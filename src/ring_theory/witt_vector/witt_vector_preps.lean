-- this should all be moved

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial.comap
import data.mv_polynomial.monad
import data.zmod.basic
import data.fintype.card
import data.finset.lattice
import data.set.disjointed
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic
import group_theory.order_of_element
import field_theory.finite
import field_theory.mv_polynomial

universes u v w u₁

-- ### FOR_MATHLIB

open_locale big_operators

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
  (q : R →+* S) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
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
  { exact char_p.int_cast_eq_zero_iff (zmod n) n, }
end

end mv_polynomial

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [comm_semiring R]



lemma equiv_of_family_aux (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (h : ∀ i, bind₁ g (f i) = X i) (φ : mv_polynomial σ R) :
  (bind₁ g) (bind₁ f φ) = φ :=
begin
  rw ← alg_hom.comp_apply,
  suffices : (bind₁ g).comp (bind₁ f) = alg_hom.id _ _,
  { rw [this, alg_hom.id_apply], },
  refine mv_polynomial.alg_hom_ext _ (alg_hom.id _ _) _,
  intro i,
  rw [alg_hom.comp_apply, alg_hom.id_apply, bind₁_X_right, h],
end

/-- I think this has been PR'd to mathlib already. If not, fix this docstring. -/
noncomputable def equiv_of_family (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, bind₁ g (f i) = X i) (hgf : ∀ i, bind₁ f (g i) = X i) :
  mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
{ to_fun    := bind₁ f,
  inv_fun   := bind₁ g,
  left_inv  := equiv_of_family_aux f g hfg,
  right_inv := equiv_of_family_aux g f hgf,
  .. bind₁ f}

@[simp] lemma equiv_of_family_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, bind₁ g (f i) = X i) (hgf : ∀ i, bind₁ f (g i) = X i) :
  (equiv_of_family f g hfg hgf : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) = bind₁ f := rfl

@[simp] lemma equiv_of_family_symm_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, bind₁ g (f i) = X i) (hgf : ∀ i, bind₁ f (g i) = X i) :
  ((equiv_of_family f g hfg hgf).symm : mv_polynomial τ R →ₐ[R] mv_polynomial σ R) = bind₁ g := rfl

@[simp] lemma equiv_of_family_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, bind₁ g (f i) = X i) (hgf : ∀ i, bind₁ f (g i) = X i)
  (φ : mv_polynomial σ R) :
  equiv_of_family f g hfg hgf φ = bind₁ f φ := rfl

@[simp] lemma equiv_of_family_symm_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, bind₁ g (f i) = X i) (hgf : ∀ i, bind₁ f (g i) = X i)
  (φ : mv_polynomial τ R) :
  (equiv_of_family f g hfg hgf).symm φ = bind₁ g φ := rfl

section monadic_stuff

open_locale classical
variables (φ : mv_polynomial σ R) (f : σ → mv_polynomial τ R)

lemma bind₁_vars : (bind₁ f φ).vars ⊆ φ.vars.bind (λ i, (f i).vars) :=
begin
  -- can we prove this using the `mono` tactic?
  -- are the lemmas above good `mono` lemmas?
  -- is `bind_mono` a good `mono` lemma?
  -- Rob: I've never used mono, so I'm not really sure...
  calc (bind₁ f φ).vars
      = (φ.support.sum (λ (x : σ →₀ ℕ), (bind₁ f) (monomial x (coeff x φ)))).vars : by { rw [← alg_hom.map_sum, ← φ.as_sum], }
  ... ≤ φ.support.bind (λ (i : σ →₀ ℕ), ((bind₁ f) (monomial i (coeff i φ))).vars) : vars_sum_subset _ _
  ... = φ.support.bind (λ (d : σ →₀ ℕ), (C (coeff d φ) * ∏ i in d.support, f i ^ d i).vars) : by simp only [bind₁_monomial]
  ... ≤ φ.support.bind (λ (d : σ →₀ ℕ), d.support.bind (λ i, (f i).vars)) : _ -- proof below
  ... ≤ φ.vars.bind (λ (i : σ), (f i).vars) : _, -- proof below
  { apply finset.bind_mono,
    intros d hd,
    calc (C (coeff d φ) * ∏ (i : σ) in d.support, f i ^ d i).vars
        ≤ (C (coeff d φ)).vars ∪ (∏ (i : σ) in d.support, f i ^ d i).vars : vars_mul _ _
    ... ≤ (∏ (i : σ) in d.support, f i ^ d i).vars : by { simp only [finset.empty_union, vars_C, finset.le_iff_subset, finset.subset.refl], }
    ... ≤ d.support.bind (λ (i : σ), (f i ^ d i).vars) : vars_prod _
    ... ≤ d.support.bind (λ (i : σ), (f i).vars) : _,
    apply finset.bind_mono,
    intros i hi,
    apply vars_pow, },
  { -- can this be golfed into a point-free proof?
    intro j,
    rw [finset.mem_bind],
    rintro ⟨d, hd, hj⟩,
    rw [finset.mem_bind] at hj,
    rcases hj with ⟨i, hi, hj⟩,
    rw [finset.mem_bind],
    refine ⟨i, _, hj⟩,
    rw [mem_vars],
    exact ⟨d, hd, hi⟩, }
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

@[simp] lemma expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
  expand p (monomial d r) = C r * ∏ i in d.support, ((X i) ^ p) ^ (d i) :=
bind₁_monomial _ _ _

lemma expand_one_apply (f : mv_polynomial σ R) : expand 1 f = f :=
by simp only [expand, bind₁_X_left, alg_hom.id_apply, ring_hom.to_fun_eq_coe,
  eval₂_hom_C_left, alg_hom.coe_to_ring_hom, pow_one, alg_hom.coe_mk]

@[simp] lemma expand_one : expand 1 = alg_hom.id R (mv_polynomial σ R) :=
by { ext1 f, rw [expand_one_apply, alg_hom.id_apply] }

lemma expand_comp_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) :
  (expand p).comp (bind₁ f) = bind₁ (λ i, expand p (f i)) :=
by { apply alg_hom_ext, intro i, simp only [alg_hom.comp_apply, bind₁_X_right], }

lemma expand_bind₁ (p : ℕ) (f : σ → mv_polynomial τ R) (φ : mv_polynomial σ R) :
  expand p (bind₁ f φ) = bind₁ (λ i, expand p (f i)) φ :=
by rw [← alg_hom.comp_apply, expand_comp_bind₁]

section
variables {S : Type*} [comm_semiring S]

@[simp]
lemma map_expand (f : R →+* S) (p : ℕ) (φ : mv_polynomial σ R) :
  map f (expand p φ) = expand p (map f φ) :=
by simp [expand, map_bind₁]

@[simp]
lemma rename_expand (f : σ → τ) (p : ℕ) (φ : mv_polynomial σ R) :
  rename f (expand p φ) = expand p (rename f φ) :=
by simp [expand, bind₁_rename, rename_bind₁]

@[simp] lemma rename_comp_expand (f : σ → τ) (p : ℕ) :
  (rename f).comp (expand p) = (expand p).comp (rename f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) :=
by { ext1 φ, simp only [rename_expand, alg_hom.comp_apply] }

open_locale classical

lemma vars_rename {τ} (f : σ → τ) (φ : mv_polynomial σ R) :
  (rename f φ).vars ⊆ (φ.vars.image f) :=
begin
  -- I guess a higher level proof might be shorter
  -- should we prove `degrees_rename` first?
  intros i,
  rw [mem_vars, finset.mem_image],
  rintro ⟨d, hd, hi⟩,
  simp only [exists_prop, mem_vars],
  contrapose! hd,
  rw [rename_eq],
  rw [finsupp.not_mem_support_iff],
  simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
  rw [finsupp.sum, finset.sum_eq_zero],
  intros d' hd',
  split_ifs with H, swap, refl,
  subst H,
  rw [finsupp.mem_support_iff, finsupp.sum_apply] at hi,
  contrapose! hi,
  rw [finsupp.sum, finset.sum_eq_zero],
  intros j hj,
  rw [finsupp.single_apply, if_neg],
  apply hd,
  exact ⟨d', hd', hj⟩
end


end

section rename
open function

lemma coeff_rename_map_domain (f : σ → τ) (hf : injective f) (φ : mv_polynomial σ R) (d : σ →₀ ℕ) :
  (rename f φ).coeff (d.map_domain f) = φ.coeff d :=
begin
  apply induction_on' φ,
  { intros u r,
    rw [rename_monomial, coeff_monomial, coeff_monomial],
    simp only [(finsupp.map_domain_injective hf).eq_iff],
    split_ifs; refl, },
  { intros, simp only [*, alg_hom.map_add, coeff_add], }
end

lemma coeff_rename_eq_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
  (h : ∀ u : σ →₀ ℕ, u.map_domain f ≠ d) :
  (rename f φ).coeff d = 0 :=
begin
  apply induction_on' φ,
  { intros u r,
    rw [rename_monomial, coeff_monomial],
    split_ifs,
    { exact (h _ ‹_›).elim },
    { refl } },
  { intros,  simp only [*, alg_hom.map_add, coeff_add, add_zero], }
end

lemma coeff_rename_ne_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
  (h : (rename f φ).coeff d ≠ 0) :
  ∃ u : σ →₀ ℕ, u.map_domain f = d :=
by { contrapose! h, apply coeff_rename_eq_zero _ _ _ h }

end rename

section
open_locale classical
variables {S : Type*} [comm_semiring S]

lemma eval₂_hom_congr' {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : mv_polynomial σ R} :
  f₁ = f₂ → (∀ i, i ∈ p₁.vars → i ∈ p₂.vars → g₁ i = g₂ i) → p₁ = p₂ →
   eval₂_hom f₁ g₁ p₁ = eval₂_hom f₂ g₂ p₂ :=
begin
  rintro rfl h rfl,
  rename [p₁ p, f₁ f],
  rw p.as_sum,
  simp only [ring_hom.map_sum, eval₂_hom_monomial],
  apply finset.sum_congr rfl,
  intros d hd,
  congr' 1,
  simp only [finsupp.prod],
  apply finset.prod_congr rfl,
  intros i hi,
  have : i ∈ p.vars, { rw mem_vars, exact ⟨d, hd, hi⟩ },
  rw h i this this,
end

end

section move_this

-- move this
variables (σ) (R)
@[simp] lemma constant_coeff_comp_C :
  constant_coeff.comp (C : R →+* mv_polynomial σ R) = ring_hom.id R :=
by { ext, apply constant_coeff_C }

@[simp] lemma constant_coeff_comp_algebra_map :
  constant_coeff.comp (algebra_map R (mv_polynomial σ R)) = ring_hom.id R :=
constant_coeff_comp_C _ _

variable {σ}

@[simp] lemma constant_coeff_rename {τ : Type*} (f : σ → τ) (φ : mv_polynomial σ R) :
  constant_coeff (rename f φ) = constant_coeff φ :=
begin
  apply φ.induction_on,
  { intro a, simp only [constant_coeff_C, rename_C]},
  { intros p q hp hq, simp only [hp, hq, ring_hom.map_add, alg_hom.map_add] },
  { intros p n hp, simp only [hp, rename_X, constant_coeff_X, ring_hom.map_mul, alg_hom.map_mul] }
end

-- @[simp] lemma constant_coeff_comp_rename {τ : Type*} (f : σ → τ) :
--   (constant_coeff : mv_polynomial τ R →+* R).comp
--   (rename f) =
--   constant_coeff :=
-- by { ext, apply constant_coeff_rename }

end move_this

end mv_polynomial


namespace finset

variables {α : Type*} [fintype α]

lemma eq_univ_of_card (s : finset α) (hs : s.card = fintype.card α) :
  s = univ :=
eq_of_subset_of_card_le (subset_univ _) $ by rw [hs, card_univ]

end finset

namespace function
variables {α β : Type*}
open set

lemma injective_of_inj_on (f : α → β) (hf : inj_on f univ) : injective f :=
λ x y h, hf (mem_univ x) (mem_univ y) h

lemma surjective_of_surj_on (f : α → β) (hf : surj_on f univ univ) : surjective f :=
begin
  intro b,
  rcases hf (mem_univ b) with ⟨a, -, ha⟩,
  exact ⟨a, ha⟩
end

end function

namespace fintype
variables {α β : Type*} [fintype α] [fintype β]
open function finset

lemma bijective_iff_injective_and_card (f : α → β) :
  bijective f ↔ injective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.1, fintype.card_congr (equiv.of_bijective f h)⟩, },
  { rintro ⟨hf, h⟩,
    refine ⟨hf, _⟩,
    let s := finset.univ.map ⟨f, hf⟩,
    have hs : s = univ := s.eq_univ_of_card (by rw [card_map, card_univ, h]),
    intro b,
    suffices : b ∈ s,
    { rw mem_map at this, rcases this with ⟨a, -, ha⟩, exact ⟨a, ha⟩ },
    rw [hs],
    exact mem_univ _ }
end

lemma bijective_iff_surjective_and_card (f : α → β) :
  bijective f ↔ surjective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.2, fintype.card_congr (equiv.of_bijective f h)⟩, },
  { rintro ⟨hf, h⟩,
    refine ⟨_, hf⟩,
    apply injective_of_inj_on,
    rintro x - y - hxy,
    apply inj_on_of_surj_on_of_card_le
      (λ a _, f a)
      (λ b _, mem_univ _) _ _ (mem_univ x) (mem_univ y) (by simpa),
    { rintro b -, obtain ⟨a, rfl⟩ := hf b, exact ⟨a, mem_univ _, rfl⟩ },
    { rw [card_univ, card_univ, h] } }
end

end fintype

section isos_to_zmod
variables (R : Type*) (n : ℕ) [comm_ring R]

lemma zmod.cast_hom_inj [char_p R n] :
  function.injective (zmod.cast_hom (show n ∣ n, by refl) R) :=
begin
  rw ring_hom.injective_iff,
  intro x,
  obtain ⟨k, rfl⟩ := zmod.int_cast_surjective x,
  rw [ring_hom.map_int_cast,
      char_p.int_cast_eq_zero_iff R n, char_p.int_cast_eq_zero_iff (zmod n) n],
  exact id,
end

lemma zmod.cast_hom_bij [fintype R] [char_p R n] (hn : fintype.card R = n) :
  function.bijective (zmod.cast_hom (show n ∣ n, by refl) R) :=
begin
  haveI : fact (0 < n) :=
  begin
    classical, by_contra H,
    erw [nat.pos_iff_ne_zero, not_not] at H,
    unfreezingI { subst H, },
    rw fintype.card_eq_zero_iff at hn,
    exact hn 0
  end,
  rw [fintype.bijective_iff_injective_and_card, zmod.card, hn, eq_self_iff_true, and_true],
  apply zmod.cast_hom_inj,
end

lemma ring_equiv.coe_ring_hom_inj {R S : Type*} [semiring R] [semiring S] (f g : R ≃+* S) :
  f = g ↔ (f : R →+* S) = g :=
begin
  refine ⟨congr_arg _, _⟩,
  rw ring_hom.ext_iff,
  intro h, ext, apply h,
end

/-- The unique ring isomorphism between `zmod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def zmod.ring_equiv [fintype R] [char_p R n] (hn : fintype.card R = n) :
  zmod n ≃+* R :=
ring_equiv.of_bijective _ (zmod.cast_hom_bij _  _ hn)

instance zmod.ring_equiv_subsingleton : subsingleton (zmod n ≃+* R) :=
⟨λ f g, by { rw ring_equiv.coe_ring_hom_inj, apply ring_hom.ext_zmod _ _ }⟩

@[simp] lemma cast_card_eq_zero [fintype R] : (fintype.card R : R) = 0 :=
begin
  have : fintype.card R •ℕ (1 : R) = 0 :=
    @pow_card_eq_one (multiplicative R) _ _ (multiplicative.of_add 1),
  simpa only [mul_one, nsmul_eq_mul]
end

lemma char_p_of_ne_zero [fintype R] (hn : fintype.card R = n) (hR : ∀ i < n, (i : R) = 0 → i = 0) :
  char_p R n :=
{ cast_eq_zero_iff :=
  begin
    have H : (n : R) = 0, by { rw [← hn, cast_card_eq_zero] },
    intros k,
    split,
    { intro h,
      rw [← nat.mod_add_div k n, nat.cast_add, nat.cast_mul, H, zero_mul, add_zero] at h,
      rw nat.dvd_iff_mod_eq_zero,
      apply hR _ (nat.mod_lt _ _) h,
      rw [← hn, gt, fintype.card_pos_iff],
      exact ⟨0⟩, },
    { rintro ⟨k, rfl⟩, rw [nat.cast_mul, H, zero_mul], }
  end }

lemma char_p_of_prime_pow_ne_zero [fintype R] (p : ℕ) [hp : fact p.prime] (n : ℕ) (hn : fintype.card R = p ^ n)
  (hR : ∀ i ≤ n, (p ^ i : R) = 0 → i = n) :
  char_p R (p ^ n) :=
begin
  obtain ⟨c, hc⟩ := char_p.exists R, resetI,
  have hcpn : c ∣ p ^ n,
  { rw [← char_p.cast_eq_zero_iff R c, ← hn, cast_card_eq_zero], },
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i, by rwa nat.dvd_prime_pow hp at hcpn,
  obtain rfl : i = n,
  { apply hR i hi, rw [← nat.cast_pow, ← hc, char_p.cast_eq_zero] },
  rwa ← hc,
end

end isos_to_zmod

lemma inv_of_commute {M : Type*} [has_one M] [has_mul M] (m : M) [invertible m] :
  commute m (⅟m) :=
calc m * ⅟m = 1       : mul_inv_of_self m
        ... = ⅟ m * m : (inv_of_mul_self m).symm

-- move this
instance invertible_pow {M : Type*} [monoid M] (m : M) [invertible m] (n : ℕ) :
  invertible (m ^ n) :=
{ inv_of := ⅟ m ^ n,
  inv_of_mul_self := by rw [← (inv_of_commute m).symm.mul_pow, inv_of_mul_self, one_pow],
  mul_inv_of_self := by rw [← (inv_of_commute m).mul_pow, mul_inv_of_self, one_pow] }

section
-- move this
lemma prod_mk_injective {α β : Type*} (a : α) :
  function.injective (prod.mk a : β → α × β) :=
by { intros b₁ b₂ h, simpa only [true_and, prod.mk.inj_iff, eq_self_iff_true] using h }
end

-- TODO: making this a global instance causes timeouts in the comm_ring instance for Witt vectors
-- :scream: :scream: :scream:
/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any `ℚ`-algebra. -/
def invertible_rat_algebra_coe_nat (R : Type*) (p : ℕ)
  [semiring R] [algebra ℚ R] [invertible (p : ℚ)] :
  invertible (p : R) :=
invertible.copy (invertible.map (algebra_map ℚ R : ℚ →* R) p) p
  (by simp only [ring_hom.map_nat_cast, coe_monoid_hom])

namespace mv_polynomial
noncomputable instance invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance invertible_rat_coe_nat (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
invertible_rat_algebra_coe_nat _ _

section
open function

variables (A B R : Type*) [comm_semiring A] [comm_semiring B] [comm_ring R] [algebra A B]

/-- `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism
`mv_polynomial A R →ₐ[R] A` obtained by `X a ↦ a`.

See `mv_polynomial.counit` for the “absolute” variant with `R = ℤ`. -/
noncomputable def acounit : mv_polynomial B A →ₐ[A] B :=
aeval id

lemma acounit_surjective : surjective (acounit A B) :=
λ a, ⟨X a, eval₂_hom_X' _ _ _⟩

/-- `mv_polynomial.counit R` is the natural surjective ring homomorphism
`mv_polynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring. -/
noncomputable def counit : mv_polynomial R ℤ →+* R :=
acounit ℤ R

lemma counit_surjective : surjective (counit R) :=
acounit_surjective ℤ R

-- TODO: we could have a similar counit for semirings over `ℕ`.

end
end mv_polynomial

lemma congr₂ {α β γ : Type*} (f : α → β → γ) (a₁ a₂ : α) (b₁ b₂ : β) :
  a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
by rintro rfl rfl; refl

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) {R : Type*} [semiring R] [hr : char_p R v] :
  nontrivial R :=
⟨⟨(1 : ℕ), 0, λ h, hv $ by rwa [char_p.cast_eq_zero_iff _ v, nat.dvd_one] at h; assumption ⟩⟩

section zmod
open mv_polynomial
variables {p : ℕ} {σ : Type*}

@[simp] lemma frobenius_zmod (p : ℕ) [hp : fact p.prime] (a : zmod p) :
  frobenius _ p a = a :=
by rw [frobenius_def, zmod.pow_card]

lemma mv_polynomial.frobenius_zmod [fact p.prime] (φ : mv_polynomial σ (zmod p)) :
  frobenius _ p φ = expand p φ :=
begin
  apply induction_on φ,
  { intro a, rw [expand_C, frobenius_def, ← C_pow, zmod.pow_card], },
  { simp only [alg_hom.map_add, ring_hom.map_add], intros _ _ hf hg, rw [hf, hg] },
  { simp only [expand_X, ring_hom.map_mul, alg_hom.map_mul],
    intros _ _ hf, rw [hf, frobenius_def], },
end

lemma mv_polynomial.expand_zmod [fact p.prime] (φ : mv_polynomial σ (zmod p)) :
  expand p φ = φ^p :=
(mv_polynomial.frobenius_zmod _).symm

-- move this
instance zmod.algebra (R : Type*) [comm_ring R] [char_p R p] : algebra (zmod p) R :=
ring_hom.to_algebra (zmod.cast_hom (dvd_refl p) R)

end zmod

lemma rat.coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = (a / b : ℚ) :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [dvd_mul_right, nat.cast_dvd_char_zero],
end

lemma ideal.mem_bot {R : Type*} [comm_ring R] {x : R} : x ∈ (⊥ : ideal R) ↔ x = 0 :=
submodule.mem_bot _


-- ### end FOR_MATHLIB
