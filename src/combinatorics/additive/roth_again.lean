import order.partition.finpartition
import topology.instances.complex
import combinatorics.additive.salem_spencer
import data.real.pi.bounds
import group_theory.finite_abelian
import data.zmod.quotient
import analysis.inner_product_space.pi_L2

noncomputable theory

section general_fourier

variables {α G : Type*} [fintype α] [comm_group G]

open_locale complex_conjugate

@[derive [comm_group]]
def character (G : Type*) [comm_group G] := G →* circle

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

lemma conj_expect [ne_zero N] : conj (𝔼 i, f i) = 𝔼 i, conj (f i) :=
by simp only [finset.expect, map_div₀, map_nat_cast, map_sum]

def inner_expect (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := 𝔼 x, conj (f x) * g x
def inner_sum' (α : Type*) [fintype α] (f g : α → ℂ) : ℂ := ∑ x, conj (f x) * g x

lemma inner_expect_eq_inner_sum {α : Type*} [fintype α] (f g : α → ℂ) :
  inner_expect α f g = inner_sum' α f g / card α := rfl

lemma character_trivial_iff {χ : character G} : χ = 1 ↔ ∀ u : G, χ u = 1 :=
by { rw fun_like.ext_iff, simp }

lemma character_nontrivial_iff {χ : character G} : χ ≠ 1 ↔ ∃ u : G, χ u ≠ 1 :=
by rw [ne.def, character_trivial_iff, not_forall]

lemma inner_sum_self {f : α → ℂ} (hf : ∀ x, (f x).abs = 1) : inner_sum' _ f f = card α :=
begin
  rw [inner_sum'],
  simp_rw [mul_comm, complex.mul_conj, complex.norm_sq_eq_abs, hf],
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
  inner_sum' G χ₁ χ₂ = 0 :=
begin
  have : χ₁⁻¹ * χ₂ ≠ 1, { rwa [ne.def, inv_mul_eq_one] },
  rw character_nontrivial_iff at this,
  obtain ⟨u, hu⟩ := this,
  simp_rw [inner_sum', coe_coe_eq, ←conj_eq_inv],
  simpa using sum_zero_of_nontrivial hu,
end

lemma inner_expect_zero_of_ne [fintype G] {χ₁ χ₂ : character G} (h : χ₁ ≠ χ₂) :
  inner_expect G χ₁ χ₂ = 0 :=
by rw [inner_expect_eq_inner_sum, inner_sum_zero_of_ne h, zero_div]

lemma inner_sum_orthogonal [fintype G] {χ₁ χ₂ : character G} :
  inner_sum' G χ₁ χ₂ = card G * if χ₁ = χ₂ then 1 else 0 :=
begin
  split_ifs,
  { rw [h, inner_sum_self, mul_one], simp },
  { rw [inner_sum_zero_of_ne h, mul_zero] }
end

lemma inner_expect_orthogonal [fintype G] {χ₁ χ₂ : character G} :
  inner_expect G χ₁ χ₂ = if χ₁ = χ₂ then 1 else 0 :=
begin
  split_ifs,
  { rw [h, inner_expect_self],
    simp only [coe_coe_eq, abs_coe_circle, forall_const] },
  { rw inner_expect_zero_of_ne h },
end

def transform [fintype G] (f : G → ℂ) (χ : character G) : ℂ := inner_expect _ f χ

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
  exact inner_sum_zero_of_ne h,
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

def mk_character_zmod {n : ℕ} (hn : 1 < n) (f : zmod n) : zmod n →+ additive circle :=
(mk_character_zmod_aux n (by linarith)).comp (add_monoid_hom.mul_left f)

def mk_character_aux {ι : Type} [fintype ι] [decidable_eq ι] {n : ι → ℕ} (hn : ∀ i, 1 < n i)
  (u : Π i : ι, zmod (n i)) :
  direct_sum ι (λ i, zmod (n i)) →+ additive circle :=
direct_sum.to_add_monoid (λ i, (mk_character_zmod (hn i) (u i)))

lemma mk_character_aux_inj {ι : Type} [fintype ι] [decidable_eq ι] {n : ι → ℕ} (hn : ∀ i, 1 < n i) :
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
  simp only [add_monoid_hom.coe_comp, add_monoid_hom.coe_coe, add_equiv.self_comp_symm, id.def, add_monoid_hom.id_apply],
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

lemma card_character_le [fintype G] : card G ≤ card (character G) :=
begin
  obtain ⟨ι, hi, n, hn, ⟨e⟩⟩ := my_classification (additive G),
  resetI,
  classical,
  let f : G → character G := monoid_hom.to_additive.symm ∘
    (λ x, (mk_character_aux hn x).comp (e : additive G →+ direct_sum ι (λ i, zmod (n i)))) ∘
      coe_fn ∘ e ∘ additive.of_mul,
  have : function.injective f,
  { refine monoid_hom.to_additive.symm.injective.comp _,
    refine function.injective.comp _
      (fun_like.coe_injective.comp (e.injective.comp additive.of_mul.injective)),
    apply comp_inj,
    apply mk_character_aux_inj },
  exact fintype.card_le_of_injective _ this,
end

lemma card_character [fintype G] : card (character G) = card G :=
begin
  classical,
  have := @finite_dimensional.fintype_card_le_finrank_of_linear_independent _ (G → ℂ) _ _ _ _ _ _ _
    lin_indep_char,
  simp only [finite_dimensional.finrank_fintype_fun_eq_card] at this,
  exact le_antisymm this card_character_le,
end

end general_fourier
