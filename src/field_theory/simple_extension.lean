import field_theory.separable
import linear_algebra.finite_dimensional
import ring_theory.adjoin

open finite_dimensional
open polynomial

/-- A computable specialization of `finsupp.emb_domain` from `fin i` to `ℕ`. -/
def finsupp.emb_fin_nat {M : Type*} [has_zero M] {i : ℕ} (f : fin i →₀ M) : ℕ →₀ M :=
{ to_fun := λ n, if h : n < i then f ⟨n, h⟩ else 0,
  support := f.support.map ⟨fin.val, fin.val_injective⟩,
  mem_support_to_fun := λ n, finset.mem_map.trans begin
    simp only [function.embedding.coe_fn_mk],
    split_ifs with h,
    { refine iff.trans _ finsupp.mem_support_iff,
      split,
      { rintros ⟨n', n'_mem, rfl⟩,
        rw fin.eta,
        exact n'_mem },
      { intro n_mem,
        exact ⟨⟨n, h⟩, n_mem, rfl⟩ } },
    { simp only [ne.def, eq_self_iff_true, not_true, iff_false, not_exists],
      rintros ⟨n', n_lt⟩ _ rfl,
      exact h n_lt },
  end }

@[simp] lemma finsupp.emb_fin_nat_apply {M : Type*} [has_zero M] {i : ℕ} (f : fin i →₀ M) (n : ℕ) :
  f.emb_fin_nat n = if h : n < i then f ⟨n, h⟩ else 0 := rfl

@[simp] lemma finsupp.emb_fin_nat_support {M : Type*} [has_zero M] {i : ℕ} (f : fin i →₀ M) :
  f.emb_fin_nat.support = f.support.map ⟨fin.val, fin.val_injective⟩ := rfl

@[simp] lemma finsupp.emb_fin_nat_sum {M N : Type*} [has_zero M] [add_comm_monoid N]
  {i : ℕ} (f : fin i →₀ M) (g : ℕ → M → N) :
  (f.emb_fin_nat).sum g = f.sum (λ i, g i) :=
begin
  simp_rw [finsupp.sum, finsupp.emb_fin_nat_support, finset.sum_map, function.embedding.coe_fn_mk],
  congr, ext j,
  congr,
  rw finsupp.emb_fin_nat_apply,
  split_ifs with h,
  { rw fin.eta },
  { exfalso,
    exact h j.2 }
end

@[simp] lemma finsupp.emb_fin_nat_eq_zero {M : Type*} [has_zero M] {i : ℕ} (f : fin i →₀ M) :
  f.emb_fin_nat = 0 ↔ f = 0 :=
begin
  rw [finsupp.ext_iff, finsupp.ext_iff],
  split; intros h n,
  { refine trans _ (h n),
    erw [finsupp.emb_fin_nat_apply, dif_pos n.2, fin.eta] },
  { by_cases hn : n < i,
    { exact trans (dif_pos hn) (h ⟨n, hn⟩) },
    { exact dif_neg hn } }
end

namespace polynomial

lemma degree_emb_fin_nat_lt {R : Type*} [semiring R] {i : ℕ} (f : fin i →₀ R) :
  degree (f.emb_fin_nat) < i :=
begin
  by_cases hf : f.emb_fin_nat = 0,
  { rw [hf, degree_zero],
    apply with_bot.bot_lt_some },
  erw [degree_eq_nat_degree hf, with_bot.some_lt_some],
  exact lt_of_not_ge (λ h, hf (leading_coeff_eq_zero.mp (dif_neg (not_lt_of_ge h))))
end

lemma eval₂_mod_by_monic_eq_self_of_root {R S : Type*} [comm_ring R] [comm_ring S] {f : R →+* S}
  {p q : polynomial R} (hq : q.monic) {x : S} (hx : q.eval₂ f x = 0) :
    (p %ₘ q).eval₂ f x = p.eval₂ f x :=
by rw [mod_by_monic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]

end polynomial

variables (R S : Type*) [comm_ring R] [comm_semiring S] [algebra R S]
variables (K L : Type*) [field K] [field L] [algebra K L]

/- A ring extension `S / R` is a simple extension if `S = R(x)` for some `x : S`. -/
@[class] def is_simple_extension : Prop :=
∃ x : S, (algebra.adjoin R {x} : subalgebra R S) = ⊤

namespace is_simple_extension

variables {R S}

lemma iff_exists_eq_aeval :
  is_simple_extension R S ↔ ∃ x : S, ∀ y : S, ∃ f : polynomial R, aeval x f = y :=
by simpa only [is_simple_extension, algebra.adjoin_singleton_eq_range, subalgebra.ext_iff,
               algebra.mem_top, iff_true] using iff.rfl

variables (R S)

/- A primitive element for `S / R` is an `x : S` such that `L = K(x)`. -/
noncomputable def primitive_element [simple : is_simple_extension R S] : S :=
classical.some simple

/- Adjoining the primitive element of `S` to `R` gives `S`. -/
lemma adjoin_primitive_element [simple : is_simple_extension R S] :
  (algebra.adjoin R {primitive_element R S} : subalgebra R S) = ⊤ :=
classical.some_spec simple

lemma mem_adjoin_primitive_element [is_simple_extension R S] (x : S) :
  x ∈ (algebra.adjoin R {primitive_element R S} : subalgebra R S) :=
(adjoin_primitive_element R S).symm ▸ algebra.mem_top

lemma adjoin_primitive_element_submodule [simple : is_simple_extension R S] :
  ((algebra.adjoin R {primitive_element R S} : subalgebra R S) : submodule R S) = ⊤ :=
by { ext, simp [mem_adjoin_primitive_element] }

lemma exists_eq_aeval_primitive_element (x : S) [is_simple_extension R S] :
  ∃ f : polynomial R, x = aeval (primitive_element R S) f :=
begin
  obtain ⟨f, hf⟩ : x ∈ (aeval (primitive_element R S)).range :=
    by simpa [algebra.adjoin_singleton_eq_range] using mem_adjoin_primitive_element R S x,
  exact ⟨f, hf.symm⟩
end

@[simp] lemma coe_aeval {S} [comm_ring S] [algebra R S] (A : subalgebra R S) (f : polynomial R) (y : A) :
  (aeval y f : S) = aeval (y : S) f :=
alg_hom_eval₂_algebra_map f A.val y

lemma is_simple_subalgebra_iff {S} [comm_ring S] [algebra R S] (A : subalgebra R S) :
  is_simple_extension R A ↔ ∃ x ∈ A, algebra.adjoin R {x} = A :=
⟨λ ⟨⟨x, mem⟩, hx⟩, ⟨x, mem, le_antisymm
  (algebra.adjoin_le (set.singleton_subset_iff.mpr mem))
  (λ y hy, begin
    have : subtype.mk y hy ∈ (⊤ : subalgebra R A) := algebra.mem_top,
    rw ← hx at this,
    rw algebra.adjoin_singleton_eq_range at this ⊢,
    obtain ⟨f, hf⟩ := this,
    use f,
    rw [subtype.ext_iff, subtype.coe_mk, coe_aeval] at hf,
    exact hf
  end)⟩,
 λ ⟨x, mem, hx⟩, ⟨⟨x, mem⟩, eq_top_iff.mpr (λ ⟨y, (hy : y ∈ A)⟩ _, begin
    rw [coe_coe, submodule.mem_coe, subalgebra.mem_to_submodule, algebra.adjoin_singleton_eq_range],
    rw [← hx, algebra.adjoin_singleton_eq_range] at hy,
    obtain ⟨f, hf⟩ := hy,
    use f,
    rw [subtype.ext_iff, coe_aeval, subtype.coe_mk],
    exact hf
  end)⟩⟩

lemma is_simple_of_bot_eq_top (h : (⊥ : subalgebra R S) = ⊤) : is_simple_extension R S :=
⟨0, trans (eq_bot_iff.mpr (algebra.adjoin_le (by simpa using subalgebra.zero_mem ⊥))) h⟩

instance is_simple_bot : is_simple_extension R (⊥ : subalgebra R S) :=
begin
  refine is_simple_of_bot_eq_top _ _ (eq_top_iff.mpr _),
  rintros ⟨x, hx⟩ _,
  obtain ⟨y, rfl⟩ := algebra.mem_bot.mp hx,
  refine algebra.mem_bot.mpr ⟨y, _⟩,
  ext,
  refl
end

end is_simple_extension

open is_simple_extension

instance finite_field.is_simple_extension [fintype L] :
  is_simple_extension K L :=
begin
  obtain ⟨x, hx⟩ := is_cyclic.exists_generator (units L),
  simp_rw ← mem_powers_iff_mem_gpowers at hx,
  refine iff_exists_eq_aeval.mpr ⟨x, λ y, _⟩,
  by_cases hy : y = 0,
  { rw hy,
    exact ⟨0, eval₂_zero _ _⟩ },
  obtain ⟨y, rfl⟩ : is_unit y := is_unit.mk0 y hy,
  obtain ⟨n, rfl⟩ := hx y,
  use X^n,
  rw [alg_hom.map_pow, aeval_X, units.coe_pow]
end

namespace is_simple_extension

section is_algebraic

variables {K L} [is_simple_extension K L] (alg : algebra.is_algebraic K L)

lemma primitive_element_is_integral : is_integral K (primitive_element K L) :=
(is_algebraic_iff_is_integral _).mp (alg (primitive_element K L))

/-- The `minimal_polynomial` of a simple algebraic extension is the minimal
polynomial of a primitive element. -/
noncomputable def minimal_polynomial : polynomial K :=
minimal_polynomial (primitive_element_is_integral alg)

/-- The `degree` of a simple algebraic extension `L / K` is the degree of the
minimal polynomial of the primitive element.

Later, in `findim_eq_simple_degree`, we will prove this is the same as the
degree of `L` over `K` as vector spaces. -/
noncomputable def simple_degree := (minimal_polynomial alg).nat_degree

/-- The `power_basis` of a simple algebraic field extension `L / K` is a basis
for `L` as a vector space of `K`, consisting of the powers of the `primitive_element`. -/
noncomputable def power_basis : fin (simple_degree alg) → L :=
λ n, primitive_element K L ^ (n : ℕ)

@[simp] lemma power_basis_apply (n : fin (simple_degree alg)) :
  power_basis alg n = primitive_element K L ^ (n : ℕ) :=
rfl

@[simp] lemma total_power_basis_eq (f : fin (simple_degree alg) →₀ K) :
  finsupp.total _ _ _ (power_basis alg) f =
    aeval (primitive_element K L) (finsupp.emb_fin_nat f) :=
by simp [aeval, eval₂_eq_sum, finsupp.total, linear_map.smul_right, algebra.smul_def]

lemma linear_independent_power_basis :
  linear_independent K (power_basis alg) :=
begin
  rw linear_independent_iff,
  intros p hp,
  rw total_power_basis_eq at hp,
  rw ← finsupp.emb_fin_nat_eq_zero,
  refine minimal_polynomial.eq_zero_of_degree_lt (primitive_element_is_integral alg) _ hp,
  rw degree_eq_nat_degree (minimal_polynomial.ne_zero _),
  exact polynomial.degree_emb_fin_nat_lt _
end

lemma mem_span_power_basis (x : L) : x ∈ submodule.span K (set.range (power_basis alg)) :=
begin
  have mp_monic := minimal_polynomial.monic (primitive_element_is_integral alg),
  have mp_ne_zero := minimal_polynomial.ne_zero (primitive_element_is_integral alg),

  obtain ⟨f, rfl⟩ := exists_eq_aeval_primitive_element K L x,
  change (eval₂ (algebra_map K L) (primitive_element K L)) f ∈
    submodule.span K (set.range (power_basis alg)),
  rw [← polynomial.eval₂_mod_by_monic_eq_self_of_root mp_monic (minimal_polynomial.aeval _),
    eval₂_eq_sum, finsupp.sum],
  refine submodule.sum_mem _ (λ i i_mem, _),
  rw ← algebra.smul_def,
  by_cases hi : i < simple_degree alg,
  { exact submodule.smul_mem _ _ (submodule.subset_span ⟨⟨i, hi⟩, rfl⟩) },
  convert submodule.zero_mem _,
  convert zero_smul _ _,
  refine coeff_eq_zero_of_degree_lt _,
  calc (f %ₘ minimal_polynomial _).degree
      < (minimal_polynomial _).degree : degree_mod_by_monic_lt _ mp_monic mp_ne_zero
  ... ≤ (minimal_polynomial _).nat_degree : degree_le_nat_degree
  ... ≤ i : with_bot.some_le_some.mpr (le_of_not_gt hi),
end

lemma power_basis_is_basis : is_basis K (power_basis alg) :=
⟨linear_independent_power_basis alg, eq_top_iff.mpr (λ x _, mem_span_power_basis alg x)⟩

lemma findim_eq_simple_degree : findim K L = simple_degree alg :=
trans (findim_eq_card_basis (power_basis_is_basis alg)) (fintype.card_fin _)

end is_algebraic

section finite_dimensional

@[simp] lemma adjoin_insert_adjoin (x : L) (s : set L) :
  algebra.adjoin K (insert x (algebra.adjoin K s : set L)) = algebra.adjoin K (insert x s) :=
begin
  refine le_antisymm (algebra.adjoin_le (set.insert_subset.mpr ⟨_, _⟩)) (algebra.adjoin_mono _),
  { exact algebra.subset_adjoin (set.mem_insert _ _) },
  { exact algebra.adjoin_mono (set.subset_insert _ _) },
  { exact set.insert_subset_insert algebra.subset_adjoin }
end

/-- Induction principle for finite dimensional fields: adjoin extra elements until finished. -/
lemma induction_on_adjoin [fd : finite_dimensional K L] {P : subalgebra K L → Prop}
  (base : P ⊥) (ih : ∀ (F : subalgebra K L) (x : L), P F → P (algebra.adjoin K (insert x F)))
  (F : subalgebra K L) : P F :=
begin
  haveI := classical.prop_decidable,
  obtain ⟨t, rfl⟩ : F.fg := F.fg_of_noetherian,
  refine finset.induction_on t _ _,
  { simpa [P'_pos] using base },
  intros x t hxt h,
  convert ih _ x h using 1,
  rw [finset.coe_insert, adjoin_insert_adjoin],
end

lemma is_simple_of_extension_eq (x y : L) (a₁ a₂ : K) (ne : a₁ ≠ a₂)
  (extension_eq : algebra.adjoin K {x + a₁ • y} = algebra.adjoin K ({x + a₂ • y} : set L)) :
  is_simple_extension K (algebra.adjoin K ({x, y} : set L)) :=
begin
  rw is_simple_subalgebra_iff,
  have z_mem : x + a₁ • y ∈ algebra.adjoin K {x, y},
  { exact subalgebra.add_mem _
    (algebra.subset_adjoin (set.mem_insert _ _))
    (subalgebra.smul_mem _ (algebra.subset_adjoin (set.subset_insert _ _ (set.mem_singleton _))) _) },
  have y_mem : y ∈ algebra.adjoin K {x + a₁ • y},
  { rw [← subalgebra.mem_to_submodule, ← submodule.smul_mem_iff _ (sub_ne_zero.mpr ne)],
    have : (a₁ - a₂) • y = (x + a₁ • y) - (x + a₂ • y) := by { rw sub_smul, ring },
    rw this,
    refine submodule.sub_mem _ (algebra.subset_adjoin (set.mem_singleton _)) _,
    rw extension_eq,
    exact algebra.subset_adjoin (set.mem_singleton _) },
  refine ⟨x + (a₁ : K) • y, z_mem,
    le_antisymm (algebra.adjoin_le (set.singleton_subset_iff.mpr z_mem))
      (algebra.adjoin_le (set.insert_subset.mpr ⟨_, set.singleton_subset_iff.mpr y_mem⟩))⟩,
  conv_lhs { rw ← add_sub_cancel x (a₁ • y) },
  refine submodule.sub_mem _ (algebra.subset_adjoin (set.mem_singleton _)) _,
  exact submodule.smul_mem _ _ y_mem
end

lemma is_simple_of_finite_intermediates_aux [finite_dimensional K L] (fin : fintype (subalgebra K L)) :
  Π (F : subalgebra K L) (inf : infinite F), is_simple_extension K F :=
begin
  refine induction_on_adjoin _ _ _ _,
  { intros, exact is_simple_extension.is_simple_bot _ _ },
  rintros F x ih inf,
  obtain hF := ih sorry,
  rw [is_simple_subalgebra_iff] at hF,
  obtain ⟨y, hy, hF⟩ := hF,
  rw [← hF, adjoin_insert_adjoin],
  set zs := { (x + (a : K) • y) | a : units K },
  set Fs := { (algebra.adjoin K ({z} : set L)) | z : zs },
  set f : zs → Fs := λ z, ⟨_, z, rfl⟩ with f_def,
  haveI inf_zs : infinite zs := sorry,
  haveI fin_Fs : fintype Fs := sorry,
  obtain ⟨⟨_, ⟨a₁, rfl⟩⟩, hz⟩ := classical.not_forall.mp (not_injective_infinite_fintype f),
  obtain ⟨⟨_, ⟨a₂, rfl⟩⟩, hz⟩ := classical.not_forall.mp hz,
  obtain ⟨Fz₁_eq_Fz₂, z₁_ne_z₂⟩ := classical.not_imp.mp hz,
  refine is_simple_of_extension_eq K L x y a₁ a₂
    (λ h, z₁_ne_z₂ (by rw [subtype.ext_iff, subtype.coe_mk, subtype.coe_mk, h])) _,
  simpa only [f_def, subtype.ext_iff, subtype.coe_mk] using Fz₁_eq_Fz₂
end

/-- Artin's primitive element theorem: if `L / K` is a finite extension
with finitely many intermediate fields `L / F / K`, then `L / K` is a simple extension. -/
lemma is_simple_of_finite_intermediates [finite_dimensional K L]
  (fin : fintype (subalgebra K L)) :
  is_simple_extension K L :=
begin
  by_cases h : nonempty (fintype L),
  { haveI : fintype L := h.some,
    apply finite_field.is_simple_extension },
  exact is_simple_of_finite_intermediates_aux (not_nonempty_fintype.mp h) fin rfl
end

/-- The primitive element theorem: if `L / K` is a separable finite extension,
it is a simple extension. -/
instance is_simple_of_is_separable [is_separable K L] [finite_dimensional K L] :
  is_simple_extension K L :=
begin
  by_cases h : cardinal.mk L < cardinal.omega,
  { haveI : fintype L := (cardinal.lt_omega_iff_fintype.mp h).some,
    apply finite_field.is_simple_extension },
end

/-- The primitive element theorem: if `K / F` is a finite extension,
it is separable iff there is a single `x : K` such that `K = F(x)`. -/
theorem separable_iff_simple :
  is_separable K L ↔ is_simple_extension K L :=
begin
  by_cases h : cardinal.mk L < cardinal.omega,
  { haveI : fintype L := (cardinal.lt_omega_iff_fintype.mp h).some,
    simp [finite_field.is_simple_extension, finite_field.is_separable] }
end

end finite_dimensional

end is_simple_extension
