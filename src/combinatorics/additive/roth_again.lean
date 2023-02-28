import order.partition.finpartition
import topology.instances.complex
import combinatorics.additive.salem_spencer
import data.real.pi.bounds
import group_theory.finite_abelian
import data.zmod.quotient
import analysis.inner_product_space.pi_L2

noncomputable theory

section general_fourier

variables {α β G : Type*}  [comm_group G]

open_locale complex_conjugate

@[derive [comm_group]]
def character (G : Type*) [comm_group G] := G →* circle

instance : monoid_hom_class (character G) G circle := monoid_hom.monoid_hom_class

instance : has_coe (G → circle) (G → ℂ) := ⟨λ χ i, (χ i : ℂ)⟩

lemma conj_eq_inv (χ : character G) {x : G} : (χ⁻¹ x : ℂ) = conj (χ x : ℂ) :=
by { rw ←coe_inv_circle_eq_conj, simp }

@[simp] lemma coe_coe_eq {χ : character G} {x : G} : (χ : G → ℂ) x = χ x := rfl

def fintype.expect {α : Type*} (s : finset α) (f : α → ℂ) : ℂ :=
s.sum f / s.card

open finset
open fintype (expect) (card)

open_locale real complex_conjugate big_operators

localized "notation `𝔼` binders ` in ` s ` with ` p:(scoped:49 p, p) `, ` r:(scoped:67 f, expect (s.filter p) f) := r" in expectations
localized "notation `𝔼` binders ` in ` s `, ` r:(scoped:67 f, expect s f) := r" in expectations
localized "notation `𝔼` binders ` with ` p:(scoped:49 p, p) `, ` r:(scoped:67 f, expect (finset.univ.filter p) f) := r" in expectations
localized "notation `𝔼` binders `, ` r:(scoped:67 f, expect finset.univ f) := r" in expectations

lemma expect_sum {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, ∑ y in t, f x y = ∑ y in t, 𝔼 x in s, f x y :=
begin
  rw [expect, sum_comm, sum_div],
  refl
end

lemma expect_comm {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, 𝔼 y in t, f x y = 𝔼 y in t, 𝔼 x in s, f x y :=
by rw [expect, expect, ←expect_sum, ←expect_sum, expect, expect,
  div_div, mul_comm, div_div, sum_comm]

lemma expect_mul {s : finset α} (f : α → ℂ) (x : ℂ) :
  (𝔼 i in s, f i) * x = 𝔼 i in s, f i * x :=
by { rw [expect, div_mul_eq_mul_div, sum_mul], refl }

lemma mul_expect {s : finset α} (f : α → ℂ) (x : ℂ) : x * (𝔼 i in s, f i) = 𝔼 i in s, x * f i :=
by simp_rw [mul_comm x, expect_mul]

lemma expect_true_univ [fintype α] {f : α → ℂ} : 𝔼 x, f x = (∑ x, f x) / card α :=
by rw [expect, card_univ]

lemma expect_indicate_eq [fintype α] [nonempty α] [decidable_eq α] (f : α → ℂ) (x : α) :
  𝔼 i, ite (x = i) (card α) 0 * f i = f x :=
begin
  simp_rw [expect_true_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)],
  rw mul_div_cancel_left,
  simp [fintype.card_ne_zero]
end

lemma expect_indicate_eq' [fintype α] [nonempty α] [decidable_eq α] (f : α → ℂ) (x : α) :
  𝔼 i, ite (i = x) (card α) 0 * f i = f x :=
by simp_rw [@eq_comm _ _ x, expect_indicate_eq]

lemma expect_congr {s : finset α} (f g : α → ℂ) (p : α → Prop) [decidable_pred p]
  (h : ∀ x ∈ s, p x → f x = g x) :
  𝔼 i in s with p i, f i = 𝔼 i in s with p i, g i :=
begin
  rw [expect, sum_congr rfl],
  { refl },
  simpa using h
end

lemma expect_congr' {s : finset α} (f g : α → ℂ) (p : α → Prop) [decidable_pred p]
  (h : ∀ x, p x → f x = g x) :
  𝔼 i in s with p i, f i = 𝔼 i in s with p i, g i :=
expect_congr _ _ _ (λ x _, h x)

-- a nondependent version of sum_bij
lemma sum_nbij {γ : Type*} [add_comm_monoid β]  {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij (λ a _, i a) hi h i_inj i_surj

lemma expect_bij {γ : Type*} {s : finset α} {t : finset γ} {f : α → ℂ} {g : γ → ℂ}
  (i : Π a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
  (𝔼 x in s, f x) = (𝔼 x in t, g x) :=
begin
  rw [expect, expect, card_congr i hi i_inj, sum_bij i hi h i_inj i_surj],
  simpa [eq_comm] using i_surj,
end

lemma expect_nbij {γ : Type*} {s : finset α} {t : finset γ} {f : α → ℂ} {g : γ → ℂ}
  (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  (𝔼 x in s, f x) = (𝔼 x in t, g x) :=
expect_bij (λ a _, i a) hi h i_inj i_surj

lemma expect_bij' {γ : Type*} {s : finset α} {t : finset γ} {f : α → ℂ} {g : γ → ℂ}
  (i : Π a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (j : Π a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
  (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
  (𝔼 x in s, f x) = (𝔼 x in t, g x) :=
begin
  rw [expect, expect, sum_bij' i hi h j hj left_inv right_inv, card_congr i hi],
  { intros a b ha hb z,
    rw [←left_inv a ha, ←left_inv b hb],
    congr' 1 },
  intros b hb,
  exact ⟨j b hb, hj _ _, right_inv _ _⟩,
end

lemma expect_nbij' {γ : Type*} {s : finset α} {t : finset γ} {f : α → ℂ} {g : γ → ℂ}
  (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (j : γ → α) (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a)
  (right_inv : ∀ a ∈ t, i (j a) = a) :
  (𝔼 x in s, f x) = (𝔼 x in t, g x) :=
expect_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

lemma expect_product' {γ : Type*} {s : finset γ} {t : finset α} {f : γ → α → ℂ} :
  (𝔼 x in s ×ˢ t, f x.1 x.2) = 𝔼 x in s, 𝔼 y in t, f x y :=
by simp only [expect, expect, card_product, sum_product', ←sum_div, div_div, mul_comm s.card,
    nat.cast_mul]

-- prod_product'
-- there are versions of this in mathlib, like exp_map_circle and exp_map_circle_hom
-- but fuck you let me be me
def e (r : ℝ) : ℂ := complex.exp (r * (2 * π * complex.I))

-- sometimes useful to write as real * I rather than real * 2πi
lemma e_eq (r : ℝ) : e r = complex.exp ((2 * π * r : ℝ) * complex.I) :=
begin
  rw [e],
  simp only [complex.of_real_mul, complex.of_real_bit0, complex.of_real_one],
  ring_nf,
end

lemma abs_e {r : ℝ} : (e r).abs = 1 := by rw [e_eq, complex.abs_exp_of_real_mul_I _]

lemma e_mem_circle {r : ℝ} : e r ∈ circle := by rw [mem_circle_iff_abs, abs_e]

lemma e_add {r s : ℝ} : e (r + s) = e r * e s :=
by rw [e, complex.of_real_add, add_mul, complex.exp_add, e, e]

lemma e_int (z : ℤ) : e z = 1 :=
by rw [e, complex.of_real_int_cast, complex.exp_int_mul_two_pi_mul_I]

lemma e_zero : e 0 = 1 := by simpa using e_int 0
lemma e_one : e 1 = 1 := by simpa using e_int 1

lemma e_add_int {r : ℝ} {z : ℤ} : e (r + z) = e r :=
by rw [e_add, e_int, mul_one]

lemma e_eq_one_iff {r : ℝ} : e r = 1 ↔ ∃ (z : ℤ), r = z :=
begin
  rw [e, complex.exp_eq_one_iff],
  simp only [mul_eq_mul_right_iff, complex.two_pi_I_ne_zero, or_false],
  split;
  { rintro ⟨n, h⟩,
    refine ⟨n, _⟩,
    exact_mod_cast h },
end

lemma conj_e {r : ℝ} : conj (e r) = e (-r) := by { rw [e, e, ←complex.exp_conj], simp }

lemma conj_expect [fintype G] {f : G → ℂ} : conj (𝔼 i, f i) = 𝔼 i, conj (f i) :=
by simp only [expect_true_univ, map_div₀, map_nat_cast, map_sum]

def inner_prod_expect (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := 𝔼 x, conj (f x) * g x
def inner_prod_sum (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := ∑ x, conj (f x) * g x

lemma inner_prod_expect_eq_inner_sum {α : Type*} [fintype α] (f g : α → ℂ) :
  inner_prod_expect α f g = inner_prod_sum α f g / card α := rfl

lemma character_trivial_iff {χ : character G} : χ = 1 ↔ ∀ u : G, χ u = 1 :=
by { rw fun_like.ext_iff, simp }

lemma character_nontrivial_iff {χ : character G} : χ ≠ 1 ↔ ∃ u : G, χ u ≠ 1 :=
by rw [ne.def, character_trivial_iff, not_forall]

lemma inner_sum_self [fintype α] {f : α → ℂ} (hf : ∀ x, (f x).abs = 1) :
  inner_prod_sum _ f f = card α :=
begin
  rw [inner_prod_sum],
  simp_rw [mul_comm, complex.mul_conj, complex.norm_sq_eq_abs, hf],
  simp [card_univ],
end

lemma inner_prod_expect_self [fintype G] {f : G → ℂ} (hf : ∀ x, (f x).abs = 1) :
  inner_prod_expect _ f f = 1 :=
begin
  rw [inner_prod_expect_eq_inner_sum, inner_sum_self hf, div_self],
  rw nat.cast_ne_zero,
  exact fintype.card_ne_zero,
end

lemma sum_eq_zero_of_nontrivial [fintype G] {χ : character G} {u : G} (hχ : χ u ≠ 1) :
  (∑ x, χ x : ℂ) = 0 :=
begin
  have : (∑ x, χ x : ℂ) = χ u * ∑ x, χ x,
  { rw [finset.mul_sum, ←equiv.sum_comp (equiv.mul_left u)],
    simp_rw [equiv.coe_mul_left, map_mul, coe_mul_unit_sphere] },
  have hχ' : (χ u : ℂ) ≠ 1, { simpa using hχ },
  exact eq_zero_of_mul_eq_self_left hχ' this.symm,
end.

lemma expect_eq_zero_of_nontrivial [fintype G] {χ : character G} {u : G} (hχ : χ u ≠ 1) :
  (𝔼 x, χ x : ℂ) = 0 :=
by rw [expect, sum_eq_zero_of_nontrivial hχ, zero_div]

lemma inner_sum_eq_zero_of_ne [fintype G] {χ₁ χ₂ : character G} (h : χ₁ ≠ χ₂) :
  inner_prod_sum G χ₁ χ₂ = 0 :=
begin
  have : χ₁⁻¹ * χ₂ ≠ 1, { rwa [ne.def, inv_mul_eq_one] },
  rw character_nontrivial_iff at this,
  obtain ⟨u, hu⟩ := this,
  simp_rw [inner_prod_sum, coe_coe_eq, ←conj_eq_inv],
  simpa using sum_eq_zero_of_nontrivial hu,
end

lemma inner_prod_expect_eq_zero_of_ne [fintype G] {χ₁ χ₂ : character G} (h : χ₁ ≠ χ₂) :
  inner_prod_expect G χ₁ χ₂ = 0 :=
by rw [inner_prod_expect_eq_inner_sum, inner_sum_eq_zero_of_ne h, zero_div]

lemma inner_sum_orthogonal [fintype G] {χ₁ χ₂ : character G} :
  inner_prod_sum G χ₁ χ₂ = if χ₁ = χ₂ then card G else 0 :=
begin
  split_ifs,
  { rw [h, inner_sum_self], simp },
  { rw [inner_sum_eq_zero_of_ne h] }
end

lemma inner_prod_expect_orthogonal [fintype G] {χ₁ χ₂ : character G} :
  inner_prod_expect G χ₁ χ₂ = if χ₁ = χ₂ then 1 else 0 :=
begin
  split_ifs,
  { rw [h, inner_prod_expect_self],
    simp only [coe_coe_eq, abs_coe_circle, forall_const] },
  { rw inner_prod_expect_eq_zero_of_ne h },
end

def transform [fintype G] (f : G → ℂ) (χ : character G) : ℂ := inner_prod_expect G χ f

lemma lin_indep_char [fintype G] : linear_independent ℂ (λ (i : character G), (i : G → ℂ)) :=
begin
  suffices : linear_independent ℂ (λ (i : character G), ((i : G → ℂ) : euclidean_space ℂ G)),
  { exact this },
  refine @linear_independent_of_ne_zero_of_inner_eq_zero _ (euclidean_space ℂ G) _ _ _ _ _ _,
  { intros χ,
    rw [ne.def, function.funext_iff],
    intro h,
    simpa using h 1 },
  intros χ₁ χ₂,
  simp only [pi_Lp.inner_apply, coe_coe_eq, is_R_or_C.inner_apply],
  intro h,
  exact inner_sum_eq_zero_of_ne h,
end

section

open_locale direct_sum

def my_thing_forward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i)) →+ ⨁ i, zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i, direct_sum.of (λ i, zmod (p i ^ n i)) i

def my_thing_backward {ι : Type} [decidable_eq ι] (p : ι → ℕ) (n : ι → ℕ) :
  (⨁ i, zmod (p i ^ n i)) →+ ⨁ (i : {i // n i ≠ 0}), zmod (p i ^ n i) :=
direct_sum.to_add_monoid $ λ i,
  if h : n i = 0 then 0 else direct_sum.of (λ (j : {i // n i ≠ 0}), zmod (p j ^ n j)) ⟨i, h⟩

lemma subsingleton_zmod_one : ∀ {n : ℕ} (x y : zmod n), n = 1 → x = y
| _ _ _ rfl := subsingleton.elim _ _

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

def mk_character_zmod_aux_aux (n : ℕ) : ℤ →+ additive circle :=
{ to_fun := λ x, additive.of_mul (⟨e (x / n), e_mem_circle⟩ : circle),
  map_zero' := by rw [int.cast_zero, zero_div, of_mul_eq_zero, subtype.ext_iff, subtype.coe_mk,
    e_zero, coe_one_unit_sphere],
  map_add' :=
  begin
    intros x y,
    rw [←of_mul_mul, equiv.apply_eq_iff_eq, submonoid.mk_mul_mk, subtype.ext_iff,
      subtype.coe_mk, subtype.coe_mk, int.cast_add, add_div, e_add],
  end }

def mk_character_zmod_aux (n : ℕ) (hn : n ≠ 0) : zmod n →+ additive circle :=
zmod.lift _ ⟨mk_character_zmod_aux_aux n,
begin
  rw [mk_character_zmod_aux_aux],
  simp only [int.cast_coe_nat, add_monoid_hom.coe_mk, set_like.coe_eq_coe, of_mul_eq_zero],
  ext : 1,
  rw [set_like.coe_mk, coe_one_unit_sphere, div_self, e_one],
  simpa using hn
end⟩

lemma zmod.lift_inj {A : Type*} [add_comm_group A] {n : ℕ} (f : {f : ℤ →+ A // f n = 0})
  (hf : ∀ i : ℤ, f i = 0 → (i : zmod n) = 0) :
  function.injective (zmod.lift n f) :=
begin
  rw [←add_monoid_hom.ker_eq_bot_iff, eq_bot_iff],
  intros i,
  simp only [add_subgroup.mem_bot, add_monoid_hom.mem_ker],
  obtain ⟨i, rfl⟩ := zmod.int_cast_surjective i,
  simp only [zmod.lift_coe],
  exact hf _
end

lemma mk_character_zmod_aux_inj {n : ℕ} (hn : n ≠ 0) :
  function.injective (mk_character_zmod_aux n hn) :=
begin
  apply zmod.lift_inj,
  intros i hi,
  rw zmod.int_coe_zmod_eq_zero_iff_dvd,
  change additive.of_mul (⟨e _, _⟩ : circle) = _ at hi,
  rw [of_mul_eq_zero, subtype.ext_iff, subtype.coe_mk, coe_one_unit_sphere, e_eq_one_iff] at hi,
  obtain ⟨z, hz⟩ := hi,
  rw [div_eq_iff, mul_comm] at hz,
  { norm_cast at hz,
    exact ⟨z, hz⟩ },
  exact_mod_cast hn
end

def mk_character_zmod {n : ℕ} (hn : n ≠ 0) (f : zmod n) : zmod n →+ additive circle :=
(mk_character_zmod_aux n hn).comp (add_monoid_hom.mul_left f)

lemma mk_character_zmod_inj {n : ℕ} (hn : n ≠ 0) :
  function.injective (mk_character_zmod hn) :=
begin
  intros x y h,
  have := fun_like.congr_fun h (1 : zmod n),
  simpa using mk_character_zmod_aux_inj hn this,
end

def mk_character_zmod_hom {n : ℕ} (hn : n ≠ 0) : zmod n →+ zmod n →+ additive circle :=
{ to_fun := mk_character_zmod hn,
  map_zero' :=
  begin
    ext x : 1,
    rw [mk_character_zmod, add_monoid_hom.coe_comp, function.comp_app, add_monoid_hom.coe_mul_left,
      zero_mul, map_zero, add_monoid_hom.zero_apply],
  end,
  map_add' := λ x y,
  begin
    ext z : 1,
    simp only [mk_character_zmod, add_monoid_hom.coe_mul_left, add_monoid_hom.coe_comp,
      add_monoid_hom.add_apply, function.comp_app, add_mul, map_add],
  end }

def mk_character_aux {ι : Type} [fintype ι] [decidable_eq ι] {n : ι → ℕ} (hn : ∀ i, n i ≠ 0)
  (u : Π i : ι, zmod (n i)) :
  direct_sum ι (λ i, zmod (n i)) →+ additive circle :=
direct_sum.to_add_monoid (λ i, (mk_character_zmod (hn i) (u i)))

lemma mk_character_aux_inj {ι : Type} [fintype ι] [decidable_eq ι] {n : ι → ℕ} (hn : ∀ i, n i ≠ 0) :
  function.injective (mk_character_aux hn) :=
begin
  intros u v h,
  ext i,
  let x : direct_sum ι (λ i, zmod (n i)) := direct_sum.of _ i 1,
  have : mk_character_aux hn u x = mk_character_aux hn v x,
  { rw h },
  simp only [mk_character_aux, direct_sum.to_add_monoid_of, mk_character_zmod,
    add_monoid_hom.coe_comp, add_monoid_hom.coe_mul_left, function.comp_app] at this,
  simpa using mk_character_zmod_aux_inj _ this,
end

lemma finite_character [finite G] : finite (character G) :=
begin
  letI : fintype G := fintype.of_finite G,
  rw ←cardinal.lt_aleph_0_iff_finite,
  have := @finite_dimensional.cardinal_mk_le_finrank_of_linear_independent ℂ (G → ℂ) _ _ _ _
    (character G) _ lin_indep_char,
  apply this.trans_lt _,
  apply cardinal.nat_lt_aleph_0,
end

instance fintype_character [fintype G] : fintype (character G) :=
@fintype.of_finite (character G) finite_character

lemma comp_symm_eq {β δ : Type*} [add_comm_group β] [add_comm_group δ] (e : δ ≃+ β) :
  (e : δ →+ β).comp (e.symm : β →+ δ) = add_monoid_hom.id β :=
begin
  ext,
  simp only [add_monoid_hom.coe_comp, add_monoid_hom.coe_coe, add_equiv.self_comp_symm, id.def,
    add_monoid_hom.id_apply],
end

-- cf https://discord.com/channels/@me/827209384811561031/1079538520353423380
lemma comp_inj {α β γ δ : Type*} [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
  (f : α → β →+ γ) (e : δ ≃+ β) (hf : function.injective f):
  function.injective (λ x : α, (f x).comp (e : δ →+ β)) :=
begin
  change function.injective ((λ i : β →+ γ, i.comp (e : δ →+ β)) ∘ f),
  refine function.injective.comp _ hf,
  intros x y h,
  dsimp at h,
  have : (x.comp (e : δ →+ β)).comp (e.symm : β →+ δ) =
    (y.comp (e : δ →+ β)).comp (e.symm : β →+ δ),
  { rw h },
  rw [add_monoid_hom.comp_assoc, add_monoid_hom.comp_assoc, comp_symm_eq] at this,
  rw add_monoid_hom.comp_id at this,
  rw add_monoid_hom.comp_id at this,
  exact this
end

variable [fintype G]

lemma card_character_le : card G ≤ card (character G) :=
begin
  obtain ⟨ι, hi, n, hn, ⟨e⟩⟩ := my_classification (additive G),
  resetI,
  classical,
  have hn' : ∀ i, n i ≠ 0, { intro i, linarith only [hn i] },
  let f : G → character G := monoid_hom.to_additive.symm ∘
    (λ x, (mk_character_aux hn' x).comp (e : additive G →+ direct_sum ι (λ i, zmod (n i)))) ∘
      coe_fn ∘ e ∘ additive.of_mul,
  have : function.injective f,
  { refine monoid_hom.to_additive.symm.injective.comp _,
    refine function.injective.comp _
      (fun_like.coe_injective.comp (e.injective.comp additive.of_mul.injective)),
    apply comp_inj,
    apply mk_character_aux_inj },
  exact fintype.card_le_of_injective _ this,
end

lemma card_character : card (character G) = card G :=
begin
  classical,
  have := @finite_dimensional.fintype_card_le_finrank_of_linear_independent _ (G → ℂ) _ _ _ _ _ _ _
    lin_indep_char,
  simp only [finite_dimensional.finrank_fintype_fun_eq_card] at this,
  exact le_antisymm this card_character_le,
end

def characters_basis (G : Type*) [comm_group G] [fintype G] : basis (character G) ℂ (G → ℂ) :=
basis_of_linear_independent_of_card_eq_finrank lin_indep_char $
  by rw [card_character, finite_dimensional.finrank_fintype_fun_eq_card]

@[simp] lemma characters_basis_apply {i : character G} : characters_basis G i = i :=
by rw [characters_basis, coe_basis_of_linear_independent_of_card_eq_finrank]

@[simps {fully_applied := ff}] def to_double_dual : G →* character (character G) := monoid_hom.eval

lemma exists_character_of_nontrivial {g : G} (hg : g ≠ 1) : ∃ χ : character G, χ g ≠ 1 :=
begin
  classical,
  by_contra' h,
  let x : G → ℂ := λ h, if g = h then 1 else 0,
  have t := (characters_basis G).sum_repr x,
  simp only [characters_basis_apply] at t,
  have t₁ := congr_fun t g,
  have t₂ := congr_fun t 1,
  simp only [fintype.sum_apply, pi.smul_apply, coe_coe_eq, h, coe_one_unit_sphere, smul_eq_mul,
    mul_one, map_one] at t₁ t₂,
  simp only [x, t₁, hg] at t₂,
  simpa using t₂,
end

lemma to_double_dual_nontrivial {g : G} (hg : g ≠ 1) : to_double_dual g ≠ 1 :=
begin
  obtain ⟨χ, hχ⟩ := exists_character_of_nontrivial hg,
  contrapose! hχ,
  simpa using fun_like.congr_fun hχ χ,
end

lemma to_double_dual_injective :
  function.injective (to_double_dual : G → character (character G)) :=
begin
  rw [←to_double_dual.ker_eq_bot_iff, eq_bot_iff],
  intro g,
  simp only [subgroup.mem_bot, monoid_hom.mem_ker],
  intro hg,
  contrapose hg,
  exact to_double_dual_nontrivial hg,
end

lemma sum_apply_of_nontrivial {x : G} (hx : x ≠ 1) : (∑ χ : character G, χ x : ℂ) = 0 :=
begin
  let x' : character (character G) := to_double_dual x,
  have : x' ≠ 1 := to_double_dual_nontrivial hx,
  rw character_nontrivial_iff at this,
  obtain ⟨χ, hχ⟩ := this,
  exact sum_eq_zero_of_nontrivial hχ,
end

lemma sum_apply_character [decidable_eq G] {x : G} :
  (∑ χ : character G, χ x : ℂ) = if x = 1 then card G else 0 :=
begin
  split_ifs,
  { rw [h],
    simp [card_univ, card_character] },
  rw [sum_apply_of_nontrivial h],
end

example [fintype α] {f : α → ℂ} (x : ℂ) : (𝔼 i, f i) * x = 𝔼 i, f i * x :=
begin
  rw expect_mul,
end

lemma parseval {f g : G → ℂ} :
  inner_prod_sum _ (transform f) (transform g) = inner_prod_expect _ f g :=
begin
  classical,
  simp_rw [inner_prod_sum, transform, inner_prod_expect, conj_expect, map_mul,
    star_ring_end_self_apply, expect_mul, mul_expect, coe_coe_eq, ←expect_sum],
  conv in (_ * _) { rw mul_mul_mul_comm },
  simp_rw [←sum_mul, ←coe_inv_circle_eq_conj, ←map_inv, ←coe_mul_unit_sphere, ←map_mul,
    sum_apply_character, mul_inv_eq_one, expect_indicate_eq],
end

lemma inversion (f : G → ℂ) (x : G) :
  ∑ (χ : character G), transform f χ * χ x = f x :=
begin
  classical,
  simp_rw [transform, inner_prod_expect, expect_mul, ←expect_sum, mul_right_comm _ (f _),
    ←sum_mul, coe_coe_eq, ←coe_inv_circle_eq_conj, ←map_inv, ←coe_mul_unit_sphere, ←map_mul,
    sum_apply_character, inv_mul_eq_one, expect_indicate_eq'],
end

def convolve (f g : G → ℂ) (x : G) : ℂ := 𝔼 y, f y * g (x * y⁻¹)

lemma convolve_eq [decidable_eq G] {f g : G → ℂ} (x : G) :
  𝔼 yz : G × G with yz.1 * yz.2 = x, f yz.1 * g yz.2 = convolve f g x :=
calc 𝔼 yz : G × G with yz.1 * yz.2 = x, f yz.1 * g yz.2 =
      𝔼 yz : G × G with yz.2 = x * yz.1⁻¹, f yz.1 * g yz.2 :
        by simp_rw [eq_mul_inv_iff_mul_eq, mul_comm]
    ... = convolve f g x :
    begin
      refine expect_nbij prod.fst (by simp) (by simp {contextual := tt}) _ (by simp),
      { rintro ⟨x, y⟩ ⟨z, w⟩,
        simp {contextual := tt} },
    end

lemma convolve_swap {f g : G → ℂ} :
  convolve f g = convolve g f :=
begin
  ext x : 1,
  refine expect_nbij (λ a, x * a⁻¹) (by simp) _ (by simp) (λ a _, ⟨x * a⁻¹, by simp⟩),
  simp [mul_comm],
end

lemma transform_convolve_apply {f g : G → ℂ} (χ : character G) :
  transform (convolve f g) χ = transform f χ * transform g χ :=
begin
  simp_rw [transform, inner_prod_expect, convolve, mul_expect, expect_mul, coe_coe_eq],
  rw [←expect_product', ←expect_product', univ_product_univ],
  refine expect_nbij' (λ x, (x.1 * x.2⁻¹, x.2)) (by simp) (λ x _, _) (λ x, (x.1 * x.2, x.2))
    (by simp) (by simp) (by simp),
  rw [mul_mul_mul_comm, ←map_mul, ←coe_mul_unit_sphere, ←map_mul, mul_left_comm x.2, mul_inv_self,
    mul_one],
end

lemma transform_convolve {f g : G → ℂ} : transform (convolve f g) = transform f * transform g :=
funext transform_convolve_apply

-- local attribute [-instance] zmod.has_coe_t
-- @[reducible] instance zmod_has_coe_t_int {n} : has_coe_t (zmod n) ℤ := zmod.has_coe_t _

def {u} scale_endo {α : Type u} [comm_monoid α] : ℕ →* monoid.End α :=
{ to_fun := λ z,
  { to_fun := λ g, g ^ z,
    map_one' := one_pow _,
    map_mul' := λ x y, mul_pow _ _ _ },
  map_one' :=
  begin
    ext g,
    simp only [pow_one, monoid_hom.coe_mk, monoid.coe_one, id.def],
  end,
  map_mul' := λ x y, by { ext g, exact pow_mul' _ _ _ } }

lemma scale_endo_apply_apply {α : Type*} [comm_monoid α] (a : ℕ) (g : α) :
  scale_endo a g = g ^ a := rfl

lemma scale_endo_add {α : Type*} [comm_monoid α] (z₁ z₂ : ℕ) (g : α) :
  scale_endo (z₁ + z₂) g = scale_endo z₁ g * scale_endo z₂ g :=
pow_add _ _ _

-- lemma scale_endo_sub (z₁ z₂ : ℤ) (g : G) :
--   scale_endo (z₁ - z₂) g = scale_endo z₁ g * (scale_endo z₂ g)⁻¹ :=
-- zpow_sub _ _ _

-- lemma scale_endo_neg (z : ℤ) (g : G) :
--   scale_endo (- z) g = (scale_endo z g)⁻¹ :=
-- zpow_neg _ _


lemma scale_endo_zero_apply {α : Type*} [comm_monoid α] (g : α) : scale_endo 0 g = 1 := pow_zero _

lemma scale_endo_one_apply {α : Type*} [comm_monoid α] (g : α) : scale_endo 1 g = g := pow_one _

lemma scale_endo_mul_apply {α : Type*} [comm_monoid α] (z₁ z₂ : ℕ) (g : α) :
  scale_endo (z₁ * z₂) g = scale_endo z₁ (scale_endo z₂ g) :=
pow_mul' _ _ _

lemma scale_endo_card (g : G) : scale_endo (card G) g = 1 := pow_card_eq_one

lemma scale_endo_mod (n : ℕ) :
  (scale_endo (n % card G) : monoid.End G) = scale_endo n :=
begin
  ext g,
  conv_rhs {rw [←nat.mod_add_div n (card G), scale_endo_add, scale_endo_mul_apply, scale_endo_card,
    mul_one] },
end

lemma scale_endo_val {m : ℕ} (h : m = card G) (n : ℕ) :
  (scale_endo (n : zmod m).val : monoid.End G) = scale_endo n :=
by rw [zmod.val_nat_cast, h, scale_endo_mod]

-- lemma zmod.coe_add {n : ℕ} {x y : zmod n} : ((x + y : zmod n) : ℤ) = (x + y) % n :=
-- by rw [←zmod.coe_int_cast, int.cast_add, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

-- lemma zmod.coe_mul {n : ℕ} {x y : zmod n} : ((x * y : zmod n) : ℤ) = (x * y) % n :=
-- by rw [←zmod.coe_int_cast, int.cast_mul, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

-- lemma zmod.coe_sub {n : ℕ} {x y : zmod n} : ((x - y : zmod n) : ℤ) = (x - y) % n :=
-- by rw [←zmod.coe_int_cast, int.cast_sub, zmod.int_cast_zmod_cast, zmod.int_cast_zmod_cast]

-- lemma zmod.coe_neg {n : ℕ} {x : zmod n} : ((- x : zmod n) : ℤ) = (- x) % n :=
-- by rw [←zmod.coe_int_cast, int.cast_neg, zmod.int_cast_zmod_cast]

lemma annoying_thing {a : ℕ} (ha : a.coprime (card G)) :
  (a * (a⁻¹ : zmod (card G)).val : zmod (card G)) = 1 :=
begin
  haveI : ne_zero (card G) := ⟨fintype.card_ne_zero⟩,
  rw [zmod.nat_cast_zmod_val, zmod.coe_mul_inv_eq_one _ ha],
end

@[simp] lemma scale_endo_invert {a : ℕ} (ha : a.coprime (card G)) (g : G) :
  scale_endo a (scale_endo (a⁻¹ : zmod (card G)).val g) = g :=
begin
  rw [←scale_endo_mul_apply, ←scale_endo_val rfl, nat.cast_mul, annoying_thing ha,
    zmod.val_one_eq_one_mod, scale_endo_mod, scale_endo_one_apply]
end

@[simp] lemma scale_endo_invert' {a : ℕ} (ha : a.coprime (card G)) (g : G) :
  scale_endo (a⁻¹ : zmod (card G)).val (scale_endo a g) = g :=
begin
  rw [←scale_endo_mul_apply, ←scale_endo_val rfl, mul_comm, nat.cast_mul, annoying_thing ha,
    zmod.val_one_eq_one_mod, scale_endo_mod, scale_endo_one_apply]
end

-- def scale_endo : zmod (card G) →* monoid.End G :=
-- { to_fun := λ z, scale_int_endo z,
--   map_one' :=
--   begin
--     ext g,
--     have : (1 : zmod (card G)) = (1 : ℤ),
--     { simp only [algebra_map.coe_one]},
--     rw [this, zmod.coe_int_cast, scale_int_endo_mod, map_one],
--   end,
--   map_mul' :=
--   begin
--     intros x y,
--     rw [zmod.coe_mul, scale_int_endo_mod, map_mul],
--   end }

-- lemma scale_endo_apply_apply (a : zmod (card G)) (g : G) : scale_endo a g = g ^ (a : ℤ) := rfl
-- lemma scale_endo_apply (a : zmod (card G)) : scale_endo a = scale_int_endo a := rfl

-- lemma scale_endo_apply_nat (a : ℤ) (g : G) : scale_endo a g = g ^ a :=
-- by { rw [scale_endo_apply, zmod.coe_int_cast, scale_int_endo_mod], refl }

-- lemma scale_endo_add_apply (z₁ z₂ : zmod (card G)) (g : G) :
--   scale_endo (z₁ + z₂) g = scale_endo z₁ g * scale_endo z₂ g :=
-- by { rw [scale_endo_apply, zmod.coe_add, scale_int_endo_mod, scale_int_endo_add], refl }

-- lemma scale_endo_sub_apply (z₁ z₂ : zmod (card G)) (g : G) :
--   scale_endo (z₁ - z₂) g = scale_endo z₁ g * (scale_endo z₂ g)⁻¹ :=
-- by { rw [scale_endo_apply, zmod.coe_sub, scale_int_endo_mod, scale_int_endo_sub], refl }

-- lemma scale_endo_neg_apply (z : zmod (card G)) (g : G) :
--   scale_endo (- z) g = (scale_endo z g)⁻¹ :=
-- by { rw [scale_endo_apply, zmod.coe_neg, scale_int_endo_mod, scale_int_endo_neg], refl }

def dilate (f : G → ℂ) (a : ℕ) (x : G) : ℂ := f (scale_endo (a⁻¹ : zmod (card G)).val x)

lemma monoid_hom.pow_apply
  {α β : Type*} [mul_one_class α] [comm_monoid β] (n : ℕ) (f : α →* β) (x : α) :
  (f ^ n) x = f x ^ n :=
rfl
-- begin
--   induction n with n ih,
--   { simp },
--   rw [pow_succ, monoid_hom.mul_apply, ih, pow_succ],
-- end

lemma scale_endo_apply_hom {α β : Type*} [comm_monoid α] [comm_monoid β]
  (a : ℕ) (f : α →* β) (x : α) :
  scale_endo a f x = f (scale_endo a x) :=
by rw [scale_endo_apply_apply, monoid_hom.pow_apply, ←monoid_hom.map_pow, scale_endo_apply_apply]

lemma transform_dilate (f : G → ℂ) (a : ℕ) (χ : character G) (ha : a.coprime (card G)) :
  transform (dilate f a) χ = transform f (scale_endo a χ) :=
begin
  simp_rw [transform, inner_prod_expect, dilate],
  refine expect_nbij' (scale_endo (a⁻¹ : zmod (card G)).val) _ _ (scale_endo a) _
    _ _,
  { simp only [mem_univ, forall_const] },
  { intros x hx,
    rw [coe_coe_eq, coe_coe_eq, scale_endo_apply_hom, scale_endo_invert ha] },
  { simp only [mem_univ, forall_const] },
  { simp only [ha, mem_univ, scale_endo_invert, eq_self_iff_true, forall_const] },
  { simp only [ha, mem_univ, scale_endo_invert', eq_self_iff_true, forall_const] },
end

def indicate (A : finset G) [decidable_pred (∈ A)] (x : G) : ℂ := if x ∈ A then 1 else 0

local notation (name := indicate) ` 𝟙 ` := indicate

lemma expect_indicate (A : finset G) [decidable_pred (∈ A)] :
  𝔼 x, 𝟙 A x = A.card / card G :=
begin
  classical,
  simp only [expect_true_univ, indicate],
  rw [←sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nat.smul_one_eq_coe],
end

lemma transform_indicate_one (A : finset G) [decidable_pred (∈ A)] :
  transform (𝟙 A) 1 = A.card / card G :=
begin
  rw [transform, inner_prod_expect, ←expect_indicate],
  simp only [coe_coe_eq, monoid_hom.one_apply, coe_one_unit_sphere, map_one, one_mul],
end

lemma inner_sum_indicate (A : finset G) [decidable_pred (∈ A)] :
  inner_prod_sum _ (transform (𝟙 A)) (transform (𝟙 A)) = A.card / card G :=
begin
  rw [parseval, inner_prod_expect],
  convert expect_indicate A using 2,
  ext x : 1,
  rw [indicate],
  split_ifs;
  simp only [map_one, mul_one, mul_zero],
end

def additive_monoid_hom {α β : Type*} [add_comm_monoid α] [comm_monoid β] :
  additive (multiplicative α →* β) ≃+ (α →+ additive β) :=
add_equiv.mk' (additive.to_mul.trans monoid_hom.to_additive'') $ λ x y, by { ext, refl }

def add_monoid_hom.to_multiplicative₂'' {α β γ : Type*}
  [add_comm_monoid α] [add_comm_monoid β] [comm_monoid γ] (f : α →+ β →+ additive γ) :
  multiplicative α →* multiplicative β →* γ :=
{ to_fun := λ a, (f a.to_add).to_multiplicative'',
  map_one' := by { ext, simp only [to_add_one, map_zero, to_mul_zero, monoid_hom.one_apply,
    add_monoid_hom.to_multiplicative''_apply_apply, add_monoid_hom.zero_apply]},
  map_mul' := λ x y, by { ext z, rw [to_add_mul, map_add], refl } }

lemma injective_thru {α β γ : Type*} [add_comm_monoid α] [add_comm_monoid β] [comm_monoid γ]
  {f : α →+ β →+ additive γ} (hf : function.injective f) :
  function.injective f.to_multiplicative₂'' :=
λ x y h, multiplicative.to_add.injective (hf (add_monoid_hom.to_multiplicative''.injective h))

def to_character {n : ℕ} (hn : n ≠ 0) :
  multiplicative (zmod n) →* character (multiplicative (zmod n)) :=
(mk_character_zmod_hom hn).to_multiplicative₂''

lemma to_character_inj {n : ℕ} (hn : n ≠ 0) :
  function.injective (to_character hn) :=
injective_thru (mk_character_zmod_inj hn)

def zmod_characters {n : ℕ} (hn : n ≠ 0) :
  multiplicative (zmod n) ≃* character (multiplicative (zmod n)) :=
mul_equiv.of_bijective (to_character hn)
begin
  haveI : ne_zero n := ⟨hn⟩,
  rw [fintype.bijective_iff_injective_and_card, card_character],
  exact ⟨to_character_inj hn, rfl⟩,
end

end general_fourier
