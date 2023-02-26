import order.partition.finpartition
import topology.instances.complex
import combinatorics.additive.salem_spencer
import data.real.pi.bounds
import group_theory.finite_abelian

noncomputable theory

section general_fourier

variables {α G : Type*} [fintype α] [comm_group G]

open_locale complex_conjugate

@[derive [comm_group]]
def character (G : Type*) [comm_group G] := monoid_hom G circle

instance : monoid_hom_class (character G) G circle := monoid_hom.monoid_hom_class

instance : has_coe (G → circle) (G → ℂ) := ⟨λ χ i, (χ i : ℂ)⟩

lemma conj_eq_inv (χ : character G) {x : G} : (χ⁻¹ x : ℂ) = conj (χ x : ℂ) :=
by { rw ←coe_inv_circle_eq_conj, simp }

@[simp] lemma coe_coe_eq {χ : character G} {x : G} : (χ : G → ℂ) x = χ x := rfl

def finset.expect {α : Type*} (s : finset α) (f : α → ℂ) : ℂ := (s.sum f) / s.card

open finset
open fintype (card)

localized "notation `𝔼` binders `, ` r:(scoped:67 f, expect univ f) := r" in big_operators

localized "notation `𝔼` binders ` in ` s `, ` r:(scoped:67 f, expect s f) := r" in big_operators

open_locale big_operators real complex_conjugate

lemma expect_sum {α β : Type*} {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, ∑ y in t, f x y = ∑ y in t, 𝔼 x in s, f x y :=
begin
  rw [expect, sum_comm, sum_div],
  refl
end

lemma expect_comm {α β : Type*} {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, 𝔼 y in t, f x y = 𝔼 y in t, 𝔼 x in s, f x y :=
by rw [expect, expect, ←expect_sum, ←expect_sum, expect, expect,
  div_div, mul_comm, div_div, sum_comm]

lemma expect_mul {α : Type*} {s : finset α} (f : α → ℂ) (x : ℂ) :
  (𝔼 i in s, f i) * x = 𝔼 i in s, f i * x :=
by { rw [expect, div_mul_eq_mul_div, sum_mul], refl }

lemma mul_expect {α : Type*} {s : finset α} (f : α → ℂ) (x : ℂ) :
  x * (𝔼 i in s, f i) = 𝔼 i in s, x * f i :=
by simp_rw [mul_comm x, expect_mul]

variables {N : ℕ} {A : finset (zmod N)} {x : zmod N} {f g : zmod N → ℂ}

def e (r : ℝ) : ℂ := complex.exp (r * (2 * π * complex.I))

lemma e_add {r s : ℝ} : e (r + s) = e r * e s :=
by rw [e, complex.of_real_add, add_mul, complex.exp_add, e, e]

lemma e_int {z : ℤ} : e z = 1 :=
by rw [e, complex.of_real_int_cast, complex.exp_int_mul_two_pi_mul_I]

lemma e_add_int {r : ℝ} {z : ℤ} : e (r + z) = e r :=
by rw [e_add, e_int, mul_one]

lemma conj_e {r : ℝ} : conj (e r) = e (-r) := by { rw [e, e, ←complex.exp_conj], simp }

lemma conj_expect [ne_zero N] : conj (𝔼 i, f i) = 𝔼 i, conj (f i) :=
by simp only [finset.expect, map_div₀, map_nat_cast, map_sum]

def inner_expect (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := 𝔼 x, f x * conj (g x)
def inner_sum (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := ∑ x, f x * conj (g x)
lemma inner_expect_eq_inner_sum {α : Type*} [fintype α] (f g : α → ℂ) :
  inner_expect α f g = inner_sum α f g / card α := rfl

lemma character_trivial_iff {χ : character G} : χ = 1 ↔ ∀ u : G, χ u = 1 :=
by { rw fun_like.ext_iff, simp }

lemma character_nontrivial_iff {χ : character G} : χ ≠ 1 ↔ ∃ u : G, χ u ≠ 1 :=
by rw [ne.def, character_trivial_iff, not_forall]

lemma inner_sum_self {f : α → ℂ} (hf : ∀ x, (f x).abs = 1) : inner_sum _ f f = card α :=
begin
  rw [inner_sum],
  simp_rw [complex.mul_conj, complex.norm_sq_eq_abs, hf],
  simp [card_univ],
end

lemma inner_expect_self [fintype G] {f : G → ℂ} (hf : ∀ x, (f x).abs = 1) : inner_expect _ f f = 1 :=
begin
  rw [inner_expect_eq_inner_sum, inner_sum_self hf, div_self],
  rw nat.cast_ne_zero,
  exact fintype.card_ne_zero,
end

lemma sum_zero_of_nontrivial [fintype G] {χ : character G} {u : G} (hχ : χ u ≠ 1) :
  (∑ x, χ x : ℂ) = 0 :=
begin
  have : (∑ x, χ x : ℂ) = χ u * ∑ x, χ x,
  { rw [finset.mul_sum, ←equiv.sum_comp (equiv.mul_left u)],
    simp_rw [equiv.coe_mul_left, map_mul, coe_mul_unit_sphere] },
  have hχ' : (χ u : ℂ) ≠ 1, { simpa using hχ },
  exact eq_zero_of_mul_eq_self_left hχ' this.symm,
end.

lemma expect_zero_of_nontrivial [fintype G] {χ : character G} {u : G} (hχ : χ u ≠ 1) :
  (𝔼 x, χ x : ℂ) = 0 :=
by rw [finset.expect, sum_zero_of_nontrivial hχ, zero_div]

lemma inner_sum_zero_of_ne [fintype G] {χ₁ χ₂ : character G} (h : χ₁ ≠ χ₂) :
  inner_sum G χ₁ χ₂ = 0 :=
begin
  have : χ₁ * χ₂⁻¹ ≠ 1, { rwa [ne.def, mul_inv_eq_one] },
  rw character_nontrivial_iff at this,
  obtain ⟨u, hu⟩ := this,
  simp_rw [inner_sum, coe_coe_eq, ←conj_eq_inv],
  simpa using sum_zero_of_nontrivial hu,
end

lemma inner_expect_zero_of_ne [fintype G] {χ₁ χ₂ : character G} (h : χ₁ ≠ χ₂) :
  inner_expect G χ₁ χ₂ = 0 :=
by rw [inner_expect_eq_inner_sum, inner_sum_zero_of_ne h, zero_div]

lemma inner_sum_orthogonal [fintype G] {χ₁ χ₂ : character G} :
  inner_sum G χ₁ χ₂ = card G * if χ₁ = χ₂ then 1 else 0 :=
begin
  split_ifs,
  { rw [h, inner_sum_self, mul_one],
    simp },
  { rw [inner_sum_zero_of_ne h, mul_zero] }
end

def transform [fintype G] (f : G → ℂ) (χ : character G) : ℂ := inner_expect _ f χ

section

open_locale direct_sum

def my_thing_forward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i)) →+ ⨁ i, zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i, direct_sum.of (λ i, zmod (p i ^ n i)) i

def my_thing_backward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ i, zmod (p i ^ n i)) →+ ⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i,
  if h : n i = 0 then 0 else direct_sum.of (λ (j : {i // n i ≠ 0}), zmod (p j ^ n j)) ⟨i, h⟩

lemma subsingleton_zmod_one {n : ℕ} (hn : n = 1) (x y : zmod n) : x = y :=
begin
  cases hn,
  simp
end

def my_thing (ι : Type) [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i)) ≃+ ⨁ i, zmod (p i ^ n i) :=
{ to_fun := my_thing_forward p n,
  inv_fun := my_thing_backward p n,
  left_inv :=
  begin
    intro x,
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp
    },
    { rw [my_thing_forward, direct_sum.to_add_monoid_of, my_thing_backward,
        direct_sum.to_add_monoid_of, dif_neg i.prop],
      cases i,
      refl },
    { rw [map_add, map_add, hx, hy] },
  end,
  right_inv :=
  begin
    intro x,
    induction x using direct_sum.induction_on with i x x y hx hy,
    { simp },
    { rw [my_thing_backward, direct_sum.to_add_monoid_of],
      split_ifs,
      { have : x = 0,
        { refine subsingleton_zmod_one _ _ _,
          rw [h, pow_zero] },
        rw [add_monoid_hom.zero_apply, map_zero, this, map_zero] },
      rw [my_thing_forward, direct_sum.to_add_monoid_of],
      refl },
    { rw [map_add, map_add, hx, hy] },
  end,
  map_add' :=
  begin
    intros x y,
    rw [map_add],
  end }

theorem my_classification (G : Type*) [add_comm_group G] [finite G] :
  ∃ (ι : Type) [fintype ι] (n : ι → ℕ) (hn : ∀ i, 1 < n i),
  nonempty $ G ≃+ direct_sum ι (λ (i : ι), zmod (n i)) :=
begin
  classical,
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := add_comm_group.equiv_direct_sum_zmod_of_fintype G,
  resetI,
  refine ⟨{i : ι // n i ≠ 0}, infer_instance, λ i, p i ^ n i, _, ⟨e.trans _⟩⟩,
  { rintro ⟨i, hi⟩,
    exact one_lt_pow (hp _).one_lt hi },
  exact (my_thing _ _ _).symm,
end

end

def finite_character [finite G] : finite (character G) :=
begin
  let G' := additive G,
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := my_classification G',
  sorry
end

end general_fourier
