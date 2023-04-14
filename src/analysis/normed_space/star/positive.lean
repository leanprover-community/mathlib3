import analysis.normed_space.star.background

.
open_locale nnreal

local notation `C⋆(` a `)` := elemental_star_algebra ℂ a
.

section cfc

open star_subalgebra

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables (a : A) [is_star_normal a] (S : star_subalgebra ℂ A)

lemma continuous_functional_calculus.spectral_mapping (f : C(spectrum ℂ a, ℂ)) :
  spectrum ℂ (continuous_functional_calculus a f) = set.range f :=
by rw [alg_equiv.spectrum_eq, continuous_map.spectrum_eq_range]

/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `star_alg_hom` from the complex-valued continuous
functions on the spectrum of `a` into `A` which sends
`(continuous_map.id ℂ).restrict (spectrum ℂ a))` to `a`, and for which
`continuous_functional_calculus a f` always lies in `elemental_algebra ℂ a`. -/
noncomputable def cfc_star_alg_hom : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A :=
C⋆(a).subtype.comp (continuous_functional_calculus a)

local notation `↑ᶜᶠᶜ` := cfc_star_alg_hom _
--noncomputable instance cfc_coe : has_coe C(spectrum ℂ a, ℂ) A := { coe := cfc_star_alg_hom a }
--lemma cfc_coe_eq_cfc_star_alg_hom (f : C(spectrum ℂ a, ℂ)) : (f : A) = cfc_star_alg_hom a f := rfl

@[simp]
lemma cfc_star_alg_hom_map_id' :
  ↑ᶜᶠᶜ((continuous_map.id ℂ).restrict (spectrum ℂ a)) = a :=
congr_arg C⋆(a).subtype (continuous_functional_calculus_map_id a)

@[simp]
lemma cfc_star_alg_hom_map_id :
  ↑ᶜᶠᶜ (continuous_map.restrict_star_alg_hom ℂ ℂ (spectrum ℂ a) (continuous_map.id ℂ)) = a :=
congr_arg C⋆(a).subtype (continuous_functional_calculus_map_id a)

variable {a}

lemma cfc_star_alg_hom_mem (f : C(spectrum ℂ a, ℂ)) : (↑ᶜᶠᶜf : A) ∈ C⋆(a) :=
(continuous_functional_calculus a f).prop

-- probably we don't actually need this lemma, but it could be convenient
lemma cfc_star_alg_hom_commute (f g : C(spectrum ℂ a, ℂ)) : commute (↑ᶜᶠᶜf) (↑ᶜᶠᶜg) :=
(commute.all f g).map $ cfc_star_alg_hom a

.
variable (a)
noncomputable def cfc_star_alg_hom₂ : C(ℂ, ℂ) →⋆ₐ[ℂ] A :=
C⋆(a).subtype.comp $
  (continuous_functional_calculus a : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] C⋆(a)).comp $
  continuous_map.restrict_star_alg_hom ℂ ℂ (spectrum ℂ a)

local notation f `[` a `]ᶜᶠᶜ` := cfc_star_alg_hom₂ a f

lemma cfc_star_alg_hom₂_mem (f : C(ℂ, ℂ)) : f[a]ᶜᶠᶜ ∈ C⋆(a) :=
(continuous_functional_calculus a $ f.restrict $ spectrum ℂ a).prop

lemma cfc_star_alg_hom₂_commute (f g : C(ℂ, ℂ)) : commute (f[a]ᶜᶠᶜ) (g[a]ᶜᶠᶜ) :=
(commute.all f g).map $ cfc_star_alg_hom₂ a

@[simp, protected] lemma star_alg_hom.coe_coe' {F R A B : Type*} [comm_semiring R] [semiring A] [algebra R A]
  [has_star A] [semiring B] [algebra R B] [has_star B] [star_alg_hom_class F R A B] (f : F) :
  ⇑(f : A →⋆ₐ[R] B) = f := rfl

lemma cfc_star_alg_hom₂_map_id : continuous_map.id ℂ [a]ᶜᶠᶜ = a :=
by { simp only [cfc_star_alg_hom₂, star_alg_hom.comp_apply,
  continuous_map.restrict_star_alg_hom_apply, star_alg_hom.coe_coe',
  continuous_functional_calculus_map_id, star_subalgebra.coe_subtype, subtype.coe_mk] }

.

lemma cfc_star_alg_hom₂_map_id_pow (n : ℕ) : ((continuous_map.id ℂ) ^ n) [a]ᶜᶠᶜ = a ^ n :=
(map_pow (cfc_star_alg_hom₂ a) (continuous_map.id ℂ) n).symm ▸
  congr_arg (λ x : A, x ^ n) (cfc_star_alg_hom₂_map_id a)


lemma cfc_star_alg_hom₂_map_const (z : ℂ) : (continuous_map.const ℂ z) [a]ᶜᶠᶜ = algebra_map ℂ A z :=
alg_hom_class.commutes (cfc_star_alg_hom₂ a) z

open polynomial
open_locale polynomial

lemma cfc_star_alg_hom₂_map_X : (X : ℂ[X]).to_continuous_map [a]ᶜᶠᶜ = a :=
by { convert cfc_star_alg_hom₂_map_id a, exact continuous_map.ext (λ x, eval_X) }

.


lemma cfc_star_alg_hom₂_map_C (z : ℂ) : (C z : ℂ[X]).to_continuous_map [a]ᶜᶠᶜ = algebra_map ℂ A z :=
by { convert cfc_star_alg_hom₂_map_const a z, exact continuous_map.ext (λ x, eval_C) }

.

lemma cfc_star_alg_hom₂_map_X_pow (n : ℕ) : (X ^ n : ℂ[X]).to_continuous_map [a]ᶜᶠᶜ = a ^ n :=
begin
  change cfc_star_alg_hom₂ a (to_continuous_map_alg_hom $ X ^ n) = a ^ n,
  simp only [map_pow],
  congr,
  exact cfc_star_alg_hom₂_map_X a,
end

lemma cfc_star_alg_hom₂_map_polynomial (p : ℂ[X]) :
  p.to_continuous_map_alg_hom [a]ᶜᶠᶜ = aeval a p :=
begin
  refine polynomial.induction_on p (λ z, _) (λ f g hf hg, by simp only [map_add, hf, hg])
    (λ n z hn, _),
  { simp only [cfc_star_alg_hom₂_map_C, to_continuous_map_alg_hom_apply, aeval_C]},
  { rw [pow_succ', ←mul_assoc, map_mul, map_mul, hn],
    simp only [cfc_star_alg_hom₂_map_X, map_mul, to_continuous_map_alg_hom_apply, aeval_X] }
end

.


lemma cfc_star_alg_hom₂_eq_of_eq_on {f g : C(ℂ, ℂ)} (h : (spectrum ℂ a).eq_on f g) :
  f[a]ᶜᶠᶜ = g[a]ᶜᶠᶜ :=
begin
  simp only [cfc_star_alg_hom₂, star_alg_hom.comp_apply],
  congr' 2,
  exact continuous_map.ext (λ x, h x.prop),
end

lemma cfc_star_alg_hom₂_eq_iff_eq_on (f g : C(ℂ, ℂ))  :
  f[a]ᶜᶠᶜ = g[a]ᶜᶠᶜ ↔ (spectrum ℂ a).eq_on f g :=
begin
  refine ⟨λ h x hx, _, cfc_star_alg_hom₂_eq_of_eq_on a⟩,
  simp only [cfc_star_alg_hom₂, star_alg_hom.comp_apply, star_alg_hom.coe_coe] at h,
  replace h := equiv_like.injective (continuous_functional_calculus a) (subtype.coe_injective h),
  simpa only using fun_like.congr_fun h ⟨x, hx⟩,
end

lemma cfc_star_alg_hom₂_spectrum_eq (f : C(ℂ, ℂ)) :
  spectrum ℂ (f[a]ᶜᶠᶜ) = f '' spectrum ℂ a :=
begin
  convert continuous_functional_calculus.spectral_mapping a
    (f.restrict $spectrum ℂ a) using 1,
  exacts [(star_subalgebra.spectrum_eq (elemental_star_algebra.is_closed ℂ a) _).symm,
    (set.range_restrict _ _).symm],
end

instance cfc_star_alg_hom₂_is_star_normal (f : C(ℂ, ℂ)) : is_star_normal (f[a]ᶜᶠᶜ) :=
⟨map_star (cfc_star_alg_hom₂ a) f ▸ cfc_star_alg_hom₂_commute a (star f) f⟩

lemma comm_mem_elemental_algebra_of_comm {x y : A} (hx : commute x a) (hx' : commute x (star a))
  (hy : y ∈ elemental_star_algebra ℂ a) : commute x y :=
begin
  refine eq_on_closure₂ _ continuous_mul (continuous_snd.mul continuous_fst) x
    (closure_singleton.symm.subst $ set.mem_singleton x : x ∈ closure {x}) y hy,
  rintro c hc b hb,
  rw set.mem_singleton_iff.1 hc,
  apply algebra.adjoin_induction hb,
  { rintro z (hz | hz),
    exacts [(set.mem_singleton_iff.1 hz).symm ▸ hx.eq,
      star_eq_iff_star_eq.1 (set.mem_singleton_iff.1 hz) ▸ hx'.eq] },
  { exact λ r, (algebra.commutes r x).symm, },
  { intros w z hw hz, simp only [mul_add, add_mul, hw, hz] },
  { intros w z hw hz, rw [←mul_assoc, hw, mul_assoc, hz, mul_assoc], },
end

.

lemma cfc_star_alg_hom₂_norm_eq (f : C(ℂ, ℂ)) : ‖f[a]ᶜᶠᶜ‖ = Sup ((λ x, ‖f x‖) '' spectrum ℂ a) :=
sorry

noncomputable def cfc_star_alg_hom₂_real : C(ℂ, ℝ) →⋆ₐ[ℝ] A :=
((cfc_star_alg_hom₂ a).restrict_scalars ℝ).comp
  (continuous_map.comp_star_alg_hom ℂ star_alg_hom.real_complex (algebra_map_clm ℝ ℂ).continuous)

@[simp]
lemma cfc_star_alg_hom₂_real_apply (f : C(ℂ, ℝ)) :
  cfc_star_alg_hom₂_real a f = ((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).comp f) [a]ᶜᶠᶜ :=
rfl

lemma cfc_star_alg_hom₂_real_is_self_adjoint (f : C(ℂ, ℝ)) :
  is_self_adjoint (cfc_star_alg_hom₂_real a f) :=
(map_star (cfc_star_alg_hom₂_real a) f).symm.trans (congr_arg _ (star_trivial f))

lemma cfc_star_alg_hom₂_real_spectrum_eq (f : C(ℂ, ℝ)) :
  spectrum ℂ (cfc_star_alg_hom₂_real a f) = (coe ∘ f) '' spectrum ℂ a :=
cfc_star_alg_hom₂_spectrum_eq a ((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).comp f)

/-- `complex.re` as a bundled continuous map. -/
@[simps]
def continuous_map.complex_re : C(ℂ, ℝ) := continuous_map.mk complex.re complex.continuous_re

/-- `complex.im` as a bundled continuous map. -/
@[simps]
def continuous_map.complex_im : C(ℂ, ℝ) := continuous_map.mk complex.im complex.continuous_im

#exit
open_locale complex_star_module

lemma cfc_star_alg_hom₂_real_map_re_comp (f : C(ℂ, ℂ)) :
  cfc_star_alg_hom₂_real a (continuous_map.complex_re.comp f) = ℜ (f[a]ᶜᶠᶜ) :=
begin
  simp only [real_part_apply_coe, ←complex.coe_smul, complex.of_real_inv, complex.of_real_bit0,
    complex.of_real_one, cfc_star_alg_hom₂_real_apply, ←map_add, ←map_star, ←map_smul],
  refine cfc_star_alg_hom₂_eq_of_eq_on a (λ x hx, _),
  simp only [complex.re_eq_add_conj, inv_mul_eq_div, continuous_map.comp_apply,
    continuous_map.complex_re_apply, continuous_map.coe_coe, algebra_map_clm_apply,
    complex.coe_algebra_map, continuous_map.coe_smul, continuous_map.coe_add,
    continuous_map.coe_id, continuous_map.coe_star, pi.smul_apply, pi.add_apply, id.def,
    pi.star_apply, is_R_or_C.star_def, algebra.id.smul_eq_mul],
end

lemma cfc_star_alg_hom₂_real_map_re : cfc_star_alg_hom₂_real a (continuous_map.complex_re) = ℜ a :=
by simpa only [cfc_star_alg_hom₂_map_id] using
  cfc_star_alg_hom₂_real_map_re_comp a (continuous_map.id ℂ)

instance self_adjoint.is_star_normal {R : Type*} [non_unital_ring R] [star_ring R]
  (x : self_adjoint R) : is_star_normal (x : R) :=
x.prop.is_star_normal

@[simp] lemma is_self_adjoint.coe_real_part {a : A} (ha : is_self_adjoint a) : (ℜ a : A) = a :=
by simpa only [real_part_apply_coe, ha.star_eq, smul_add]
  using inv_of_two_smul_add_inv_of_two_smul ℝ a

@[simp] lemma is_self_adjoint.coe_imaginary_part {a : A} (ha : is_self_adjoint a) : (ℑ a : A) = 0 :=
by simp only [imaginary_part_apply_coe, ha.star_eq, sub_self, smul_zero]

noncomputable instance c_star_algebra.has_pos_part : has_pos_part A :=
{ pos := λ a, cfc_star_alg_hom₂_real (ℜ a : A) (continuous_map.complex_re⁺) }

lemma pos_part_def (a : A) : a⁺ = cfc_star_alg_hom₂_real (ℜ a : A) (continuous_map.complex_re⁺) :=
rfl

noncomputable instance c_star_algebra.has_neg_part : has_neg_part A :=
{ neg := λ a, cfc_star_alg_hom₂_real (ℜ a : A) (continuous_map.complex_re⁻) }

lemma neg_part_def (a : A) : a⁻ = cfc_star_alg_hom₂_real (ℜ a : A) (continuous_map.complex_re⁻) :=
rfl

instance {X Y : Type*} [topological_space X] [topological_space Y] [has_add Y]
  [has_continuous_add Y] [partial_order Y] [covariant_class Y Y (+) (≤)] :
  covariant_class C(X, Y) C(X, Y) (+) (≤) :=
{ elim := λ f g h h' x, add_le_add_left (h' x) _ }

lemma pos_part_mul_neg_part (a : A) : a⁺ * a⁻ = 0 :=
begin
  suffices : continuous_map.complex_re⁺ * continuous_map.complex_re⁻ = 0,
  { simp only [pos_part_def, neg_part_def, ←map_mul, this, map_zero] },
  ext1 x,
  simp only [continuous_map.coe_mul, pi.mul_apply, continuous_map.coe_zero, pi.zero_apply,
    mul_eq_zero, lattice_ordered_comm_group.pos_part_def,
      lattice_ordered_comm_group.neg_part_def],
  by_cases h : x.re ≤ 0,
  exacts [or.inl (max_eq_right h), or.inr (max_eq_right (neg_neg_of_pos (not_le.1 h)).le)],
end

lemma pos_part_sub_neg_part (a : A) : a⁺ - a⁻ = ℜ a :=
by rw [pos_part_def, neg_part_def, ←map_sub, lattice_ordered_comm_group.pos_sub_neg,
  cfc_star_alg_hom₂_real_map_re, (ℜ a).prop.coe_real_part]

lemma pos_part_neg (a : A) : (-a)⁺ = a⁻ :=
begin
  simp only [pos_part_def, map_neg, add_subgroup.coe_neg],
  sorry,
  -- oof, actually this is hard because we need composition. I think we need some sort of
  -- uniqueness result for the CFC.
end

lemma neg_part_neg (a : A) : (-a)⁻ = a⁺ :=
by simpa only [←pos_part_sub_neg_part, neg_sub, pos_part_neg, sub_right_inj]
  using (show (ℜ (-a) : A) = - ℜ a, from congr_arg coe (map_neg _ a))

open complex

lemma star_ordered_ring.is_self_adjoint_of_nonneg {R : Type*} [non_unital_ring R] [partial_order R]
  [star_ordered_ring R] {x : R} (h : 0 ≤ x) : is_self_adjoint x :=
begin
  obtain ⟨y, rfl⟩ := (star_ordered_ring.nonneg_iff x).1 h,
  exact is_self_adjoint.star_mul_self y,
end

end cfc

namespace is_self_adjoint

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]

-- which of these versions do we prefer?
lemma coe_spectrum_real {a : A} (ha : is_self_adjoint a) :
  coe '' spectrum ℝ a = spectrum ℂ a :=
begin
  refine set.subset.antisymm _ (λ x hx, _),
  { rintro _ ⟨x, hx, rfl⟩, exact spectrum.mem_real_iff_complex.1 hx },
  { lift x to ℝ using (ha.mem_spectrum_eq_re hx).symm ▸ complex.of_real_im x.re,
    exact ⟨x, spectrum.mem_real_iff_complex.2 hx, rfl⟩, }
end

-- which of these versions do we prefer?
lemma spectrum_re {a : A} (ha : is_self_adjoint a) :
  complex.re '' spectrum ℂ a = spectrum ℝ a :=
begin
  refine set.subset.antisymm _
    (λ x hx, ⟨(x : ℂ), spectrum.mem_real_iff_complex.1 hx, complex.of_real_re x⟩),
  rintro _ ⟨x, hx, rfl⟩,
  exact spectrum.mem_real_iff_complex.2 (ha.mem_spectrum_eq_re hx ▸ hx),
end

-- yuck `is_self_adjoint.is_star_normal` needs to be protected
/-- A element in a C⋆-algebra is self-adjoint if and only if it is normal has its spectrum is
real. -/
lemma star_normal_and_spectrum_real_iff {a : A} :
  _root_.is_star_normal a ∧ (coe '' spectrum ℝ a = spectrum ℂ a) ↔ is_self_adjoint a :=
begin
  refine ⟨_, λ ha, ⟨ha.is_star_normal, ha.coe_spectrum_real⟩⟩,
  unfreezingI { rintro ⟨a_normal, ha⟩ },
  refine cfc_star_alg_hom_map_id a ▸ is_self_adjoint.star_hom_apply _ _,
  rw ← ha,
  ext1 x,
  rcases x.prop with ⟨y, -, hy⟩,
  simp only [←hy, continuous_map.star_apply, continuous_map.restrict_star_alg_hom_apply,
    continuous_map.coe_restrict, continuous_map.coe_id, function.comp.left_id, is_R_or_C.star_def,
    is_R_or_C.conj_of_real],
end

lemma re_mem_spectrum {a : A} (ha : is_self_adjoint a) {x : ℂ} (hx : x ∈ spectrum ℂ a) :
  x.re ∈ spectrum ℝ a :=
spectrum.mem_real_iff_complex.2 $ ha.mem_spectrum_eq_re hx ▸ hx

def homeo_spectrum_complex_real {a : A} (ha : is_self_adjoint a) :
  spectrum ℂ a ≃ₜ spectrum ℝ a :=
{ to_fun := subtype.map complex.re $ λ _, ha.re_mem_spectrum,
  inv_fun := subtype.map coe (λ _, spectrum.mem_real_iff_complex.1),
  left_inv := λ x, subtype.ext $
    by rw [subtype.map_coe, subtype.map_coe, ←ha.mem_spectrum_eq_re x.prop],
  right_inv := λ x, subtype.ext $ by simp only [subtype.map_coe, complex.of_real_re],
  continuous_to_fun := complex.continuous_re.subtype_map $ λ _, ha.re_mem_spectrum,
  continuous_inv_fun := is_R_or_C.continuous_of_real.subtype_map $
    λ _, spectrum.mem_real_iff_complex.1 }

@[simp] lemma coe_homeo_spectrum_complex_real {a : A} (ha : is_self_adjoint a) :
  (ha.homeo_spectrum_complex_real : spectrum ℂ a → spectrum ℝ a) =
  subtype.map complex.re (λ _, ha.re_mem_spectrum) :=
rfl

@[simp] lemma coe_homeo_spectrum_complex_real_symm {a : A} (ha : is_self_adjoint a) :
  (ha.homeo_spectrum_complex_real.symm : spectrum ℝ a → spectrum ℂ a) =
  subtype.map coe (λ _, spectrum.mem_real_iff_complex.1) :=
rfl

open_locale complex_order

lemma spectrum_subset_Icc {a : A} (ha : is_self_adjoint a) :
  spectrum ℂ a ⊆ set.Icc (-‖a‖ : ℂ) (‖a‖) :=
begin
  nontriviality A,
  intros x hx,
  have hx' := ha.mem_spectrum_eq_re hx,
  rw [ha.mem_spectrum_eq_re hx, set.mem_Icc, complex.real_le_real, ←complex.of_real_neg,
    complex.real_le_real, and_comm, neg_le, ←abs_le', ←real.norm_eq_abs],
  have : ‖(x.re : ℂ)‖ ≤ ‖a‖ := hx' ▸ spectrum.norm_le_norm_of_mem hx,
  simpa only [is_R_or_C.norm_of_real] using this,
end

end is_self_adjoint

section cfc2

open_locale complex_star_module
open complex

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [partial_order A] [star_ordered_ring A] [cstar_ring A] [star_module ℂ A]

lemma imaginary_part_eq_of_le {a b : A} (h : a ≤ b) :
  ℑ a = ℑ b :=
begin
  rw [←sub_eq_zero, ←neg_eq_zero, neg_sub, ←map_sub],
  exact subtype.ext (star_ordered_ring.is_self_adjoint_of_nonneg $
    sub_nonneg.2 h).coe_imaginary_part,
end

lemma real_part_le_real_part_iff (a b : A) :
  (ℜ a : A) ≤ ℜ b ∧ ℑ a = ℑ b ↔ a ≤ b :=
begin
  rw [←add_le_add_iff_right (I • (ℑ a : A)), real_part_add_I_smul_imaginary_part],
  refine ⟨λ h, real_part_add_I_smul_imaginary_part b ▸ h.2 ▸ h.1,
    λ h, _⟩,
  exact let him := imaginary_part_eq_of_le h in
    ⟨by simpa only [him, real_part_add_I_smul_imaginary_part] using h, him⟩,
end

end cfc2

#exit
section positive

open_locale complex_order
variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]

lemma is_self_adjoint.norm_sub_algebra_map_le_iff {a : A} (ha : is_self_adjoint a) {z : ℝ}
  (hz : ‖a‖ ≤ z) :
  (‖a - algebra_map ℂ A z‖ ≤ z) ↔ spectrum ℂ a ⊆ set.Ici (0 : ℂ) :=
begin
  unfreezingI { rcases subsingleton_or_nontrivial A with (hA | hA) },
  { simp only [subsingleton.elim (algebra_map ℂ A z) 0, complex.real_le_real, hz,
      spectrum.of_subsingleton, set.empty_subset, sub_zero], },
  haveI := ha.is_star_normal,
  conv_lhs { rw [←cfc_star_alg_hom₂_map_id a, ←cfc_star_alg_hom₂_map_const a, ←map_sub,
    cfc_star_alg_hom₂_norm_eq] },
  rw cSup_le_iff _ ((spectrum.nonempty a).image _),
  { refine ⟨λ h, _, λ h, _⟩,
    { intros y hy,
      specialize h _ ⟨y, hy, rfl⟩,
      simp only [continuous_map.coe_sub, continuous_map.coe_id, continuous_map.coe_const,
        pi.sub_apply, id.def, function.const_apply] at h,
      have hy' := ha.mem_spectrum_eq_re hy,
      rw hy' at h ⊢,
      rw [←complex.of_real_sub, is_R_or_C.norm_of_real, real.norm_eq_abs, abs_le] at h,
      exact complex.zero_le_real.2 ((sub_le_sub_iff_right z).1 (neg_eq_zero_sub z ▸ h.1)) },
    { rintro _ ⟨y, hy, rfl⟩,
      simp only [continuous_map.coe_sub, continuous_map.coe_id, continuous_map.coe_const,
        pi.sub_apply, id.def, function.const_apply],
      have hy' := ha.mem_spectrum_eq_re hy,
      rw hy' at hy ⊢,
      replace hy' : 0 ≤ y.re := complex.real_le_real.1 (h hy),
      rw [←complex.of_real_sub, is_R_or_C.norm_of_real, real.norm_of_nonpos, neg_sub],
      exact sub_le_self z hy',
      rw [sub_nonpos, ←real.norm_of_nonneg hy', ←@is_R_or_C.norm_of_real ℂ],
      exact (spectrum.norm_le_norm_of_mem hy).trans hz } },
  { use ‖a‖ + ‖(z : ℂ)‖,
    rintro _ ⟨x, hx, rfl⟩,
    exact (norm_sub_le _ _).trans (add_le_add_right (spectrum.norm_le_norm_of_mem hx) _), }
end

structure is_positive (a : A) : Prop :=
(is_self_adjoint' : is_self_adjoint a)
(spectrum_nonneg' : spectrum ℂ a ⊆ set.range (coe : ℝ≥0 → ℂ))

namespace is_positive

variables {a : A} (ha : is_positive a)

-- do we actually need this separate lemma?
protected lemma is_self_adjoint : is_self_adjoint a :=
ha.is_self_adjoint'

lemma spectrum_nonneg : spectrum ℂ a ⊆ set.range (coe : ℝ≥0 → ℂ) :=
ha.spectrum_nonneg'

lemma coe_nnreal_spectrum (ha : is_positive a) : coe '' spectrum ℝ≥0 a = spectrum ℂ a :=
set.subset.antisymm
  (by { rintro _ ⟨x, hx, rfl⟩, exact spectrum.mem_nnreal_iff_complex.1 hx })
  begin
    intros x hx,
    obtain ⟨x, rfl⟩ := ha.spectrum_nonneg' hx,
    exact ⟨x, spectrum.mem_nnreal_iff_complex.2 hx, rfl⟩,
  end

protected lemma is_star_normal : is_star_normal a := ha.is_self_adjoint.is_star_normal

lemma to_nnreal_spectrum_real {a : A} (ha : is_positive a) :
  real.to_nnreal '' spectrum ℝ a = spectrum ℝ≥0 a :=
begin
  rw [← ha.is_self_adjoint.spectrum_re, set.image_image, ←ha.coe_nnreal_spectrum, set.image_image],
  simp only [coe_coe, complex.of_real_re, real.to_nnreal_coe, set.image_id'],
end

lemma star_normal_and_spectrum_nonneg_iff {a : A} :
  is_star_normal a ∧ spectrum ℂ a ⊆ set.range (coe : ℝ≥0 → ℂ) ↔ is_positive a :=
begin
  refine ⟨λ ha, _, λ ha, ⟨ha.is_star_normal, ha.spectrum_nonneg⟩⟩,
  { rcases ha with ⟨ha₁, ha₂⟩,
    refine ⟨is_self_adjoint.star_normal_and_spectrum_real_iff.1 ⟨ha₁, _⟩, ha₂⟩,
    refine set.ext (λ z, ⟨_, λ hz, _⟩),
    { rintro ⟨x, hx, rfl⟩, exact spectrum.mem_real_iff_complex.1 hx },
    -- we'll fix this later
    sorry { rw ←ha₂ at hz,
      rcases hz with ⟨x, hx, rfl⟩,
      exact ⟨(x : ℝ), spectrum.mem_nnreal_iff_real.1 hx, rfl⟩, } },
end

lemma iff_is_self_adjoint_and_spectrum_nonneg {a : A} :
  is_positive a ↔ (is_self_adjoint a ∧ spectrum ℂ a ⊆ set.range (coe : ℝ≥0 → ℂ)) :=
⟨λ h, ⟨h.is_self_adjoint, h.spectrum_nonneg⟩, λ h, ⟨h.1, h.2⟩⟩

lemma norm_sub_algebra_map_le {a : A} (ha : is_positive a) {z : ℝ} (hz : ‖a‖ ≤ z) :
  ‖a - algebra_map ℂ A z‖ ≤ z :=
(ha.is_self_adjoint.norm_sub_algebra_map_le_iff hz).2 $
  complex.Ici_zero_eq_range_coe.symm ▸ ha.spectrum_nonneg

lemma _root_.is_self_adjoint.is_positive_of_norm_sub_algebra_map_le {a : A} (ha : is_self_adjoint a)
  {z : ℝ} (hz : ‖a‖ ≤ z) (h : ‖a - algebra_map ℂ A z‖ ≤ z) : is_positive a :=
⟨ha, complex.Ici_zero_eq_range_coe ▸ (ha.norm_sub_algebra_map_le_iff hz).1 h⟩

lemma iff_is_self_adjoint_and_norm_sub_algebra_map_le {a : A} :
  is_self_adjoint a ∧ ‖a - algebra_map ℂ A (‖a‖)‖ ≤ ‖a‖ ↔ is_positive a :=
⟨λ h, h.1.is_positive_of_norm_sub_algebra_map_le le_rfl h.2,
 λ h, ⟨h.is_self_adjoint, h.norm_sub_algebra_map_le le_rfl⟩⟩

lemma add {a b : A} (ha : is_positive a) (hb : is_positive b) : is_positive (a + b) :=
begin
  refine (ha.is_self_adjoint.add hb.is_self_adjoint).is_positive_of_norm_sub_algebra_map_le
    (norm_add_le a b) _,
  rw [complex.of_real_add, map_add, add_sub_add_comm],
  exact (norm_add_le _ _).trans
    (add_le_add (ha.norm_sub_algebra_map_le le_rfl) (hb.norm_sub_algebra_map_le le_rfl))
end

protected lemma is_closed : is_closed {a : A | is_positive a} :=
begin
  simp only [←iff_is_self_adjoint_and_norm_sub_algebra_map_le, is_self_adjoint, set.set_of_and],
  refine (is_closed_eq continuous_star continuous_id).inter (is_closed_le _ continuous_norm),
  refine (continuous_id.sub $ (algebra_map_clm ℂ A).continuous.comp _).norm,
  exact complex.continuous_of_real.comp continuous_norm,
end

lemma _root_.complex.star_eq_self_of_nonneg {z : ℂ} (hz : 0 ≤ z) : star z = z :=
begin
  lift z to ℝ using (complex.le_def.2 hz).2.symm,
  exact complex.conj_of_real z,
end

instance _root_.complex.nnreal.can_lift : can_lift ℂ ℝ≥0 coe (λ z, 0 ≤ z) :=
{ prf := λ z hz,
  begin
    lift z to ℝ using (complex.le_def.2 hz).2.symm,
    lift z to ℝ≥0 using (complex.zero_le_real.1 hz),
    exact ⟨z, rfl⟩,
  end }

lemma cfc_of_nonneg_on_spectrum {a : A} [is_star_normal a] {f : C(ℂ, ℂ)}
  (hf : ∀ x ∈ spectrum ℂ a, 0 ≤ f x) : is_positive (cfc_star_alg_hom₂ a f) :=
begin
  refine ⟨_, _⟩,
  rw [is_self_adjoint, ←map_star],
  refine cfc_star_alg_hom₂_eq_of_eq_on a (λ x hx, _root_.complex.star_eq_self_of_nonneg $ hf x hx),
  rw cfc_star_alg_hom₂_spectrum_eq,
  rintro _ ⟨x, hx, rfl⟩,
  lift (f x) to ℝ≥0 using hf x hx,
  exact ⟨_x, rfl⟩,
end

lemma cfc_real_of_nonneg_on_spectrum {a : A} [is_star_normal a] {f : C(ℂ, ℝ)}
  (hf : ∀ x ∈ spectrum ℂ a, 0 ≤ f x) : is_positive (cfc_star_alg_hom₂_real a f) :=
begin
  refine ⟨cfc_star_alg_hom₂_real_is_self_adjoint a f, _⟩,
  rw cfc_star_alg_hom₂_real_spectrum_eq,
  rintro _ ⟨x, hx, rfl⟩,
  exact ⟨⟨f x, hf x hx⟩, rfl⟩,
end

lemma pos_part_is_positive (a : A) [is_star_normal a] : is_positive (a⁺) :=
cfc_real_of_nonneg_on_spectrum (λ _ _, le_max_right _ _)

lemma neg_part_is_positive (a : A) [is_star_normal a] : is_positive (a⁻) :=
cfc_real_of_nonneg_on_spectrum (λ _ _, le_max_right _ _)

open complex

lemma real_smul (ha : is_positive a) {r : ℝ} (hr : 0 ≤ r) : is_positive (r • a) :=
begin
  refine ⟨ha.is_self_adjoint.smul r, _⟩,
  nontriviality A,
  rw [←complex.coe_smul, spectrum.smul_eq_smul _ _ (spectrum.nonempty a)],
  rintro _ ⟨x, hx, rfl⟩,
  obtain ⟨x, rfl⟩ := ha.spectrum_nonneg hx,
  exact ⟨⟨r, hr⟩ * x, by simp only [coe_coe, nonneg.coe_mul, subtype.coe_mk, of_real_mul, coe_smul,
    is_R_or_C.of_real_smul]⟩,
end

lemma nnreal_smul (ha : is_positive a) (r : ℝ≥0) : is_positive (r • a) := ha.real_smul r.prop

lemma nat_smul (ha : is_positive a) (n : ℕ) : is_positive (n • a) :=
(nsmul_eq_smul_cast ℝ≥0 n a).symm ▸ ha.nnreal_smul (n : ℝ≥0)

-- wrong namespace
lemma eq_scalar_of_spectrum_subset {a : A} [is_star_normal a] {z : ℂ}
  (h : spectrum ℂ a ⊆ {z}) : a = algebra_map ℂ A z :=
begin
  rw [←cfc_star_alg_hom₂_map_id a, ←cfc_star_alg_hom₂_map_const a z],
  exact cfc_star_alg_hom₂_eq_of_eq_on a (λ x hx, set.mem_singleton_iff.1 (h hx)),
end

-- wrong namespace
lemma eq_one_of_spectrum_subset {a : A} [is_star_normal a] (h : spectrum ℂ a ⊆ {1}) : a = 1 :=
map_one (algebra_map ℂ A) ▸ eq_scalar_of_spectrum_subset h

-- wrong namespace
lemma eq_zero_of_spectrum_subset {a : A} [is_star_normal a] (h : spectrum ℂ a ⊆ {0}) : a = 0 :=
map_zero (algebra_map ℂ A) ▸ eq_scalar_of_spectrum_subset h

lemma eq_zero_of_is_positive_neg (ha : is_positive a) (ha' : is_positive (-a)) : a = 0 :=
begin
  obtain ⟨h, h'⟩ := ⟨ha.spectrum_nonneg, ha'.spectrum_nonneg⟩,
  rw [←complex.Ici_zero_eq_range_coe] at h h',
  rw [←spectrum.neg_eq, set.neg_subset, ←set.image_neg, set.image_neg_Ici, neg_zero] at h',
  letI := ha.is_self_adjoint.is_star_normal,
  exact eq_zero_of_spectrum_subset (λ x hx, le_antisymm (h' hx) (h hx)),
end

lemma _root_.is_self_adjoint.is_positive_sq {a : A} (ha : is_self_adjoint a) :
  is_positive (a ^ 2) :=
begin
  letI := ha.is_star_normal,
  rw [←cfc_star_alg_hom₂_map_id_pow a 2],
  refine cfc_of_nonneg_on_spectrum (λ x hx, (_ : 0 ≤ x ^ 2)),
  lift x to ℝ using complex.of_real_im x.re ▸ congr_arg complex.im (ha.mem_spectrum_eq_re hx),
  rw [←complex.of_real_pow, complex.zero_le_real],
  exact sq_nonneg x,
end

theorem _root_.spectrum.mul_eq_swap_mul_union_zero (𝕜 : Type*) {A : Type*} [field 𝕜] [ring A]
  [algebra 𝕜 A] (a b : A) : spectrum 𝕜 (a * b) ∪ {0} = spectrum 𝕜 (b * a) ∪ {0} :=
by simpa only [set.diff_union_self] using
  congr_arg (λ s, s ∪ ({0} : set 𝕜)) (spectrum.nonzero_mul_eq_swap_mul a b)

open_locale complex_star_module
-- wrong namespace
lemma eq_zero_of_is_positive_neg_star_mul_self {a : A} (ha : is_positive (-(star a * a))) : a = 0 :=
begin
  rw ←cstar_ring.star_mul_self_eq_zero_iff,
  refine is_positive.eq_zero_of_is_positive_neg _ ha,
  have : 2 • (ℜ a : A) ^ 2 + 2 • (ℑ a) ^ 2 = star a * a + a * star a,
  { conv_rhs { rw ←real_part_add_I_smul_imaginary_part a },
    simp only [star_add, star_smul, (ℜ a).prop.star_eq, (ℑ a).prop.star_eq, mul_add, add_mul, ←sq,
      complex.star_def, complex.conj_I, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul,
      mul_neg, neg_mul, complex.I_mul_I, neg_neg, one_smul],
    simp only [neg_smul],
    abel },
  rw ←sub_eq_iff_eq_add at this,
  rw [←this, sub_eq_add_neg],
  have : is_positive (-(a * star a)),
  { refine ⟨(is_self_adjoint.mul_star_self a).neg, _⟩,
    refine (set.subset_union_left _ ({0} : set ℂ)).trans _,
    rw [←neg_mul, _root_.spectrum.mul_eq_swap_mul_union_zero, mul_neg],
    exact set.union_subset ha.spectrum_nonneg (set.singleton_subset_iff.2 ⟨0, rfl⟩) },
  exact (((ℜ a).prop.is_positive_sq.nat_smul 2).add $
    (ℑ a).prop.is_positive_sq.nat_smul 2).add this,
end
.

lemma spectrum_real_nonneg (ha : is_positive a) : spectrum ℝ a ⊆ set.range (coe : ℝ≥0 → ℝ) :=
begin
  rw spectrum.real_eq_preimage_coe_complex,
  intros x hx,
  obtain ⟨y, hy⟩ := ha.spectrum_nonneg hx,
  exact ⟨y, complex.of_real_injective hy⟩,
end

protected lemma zero : is_positive (0 : A) :=
⟨(0 : self_adjoint A).prop,
  by { nontriviality A, rw spectrum.zero_eq, exact set.singleton_subset_iff.2 ⟨0, rfl⟩ }⟩

protected lemma one : is_positive (1 : A) :=
begin
  refine ⟨is_self_adjoint_one A, _⟩,
  nontriviality A,
  rw spectrum.one_eq,
  exact set.singleton_subset_iff.2 ⟨1, rfl⟩,
end

protected lemma pow (ha : is_positive a) (n : ℕ) : is_positive (a ^ n) :=
begin
  cases n,
  { rw pow_zero, exact is_positive.one },
  refine ⟨ha.is_self_adjoint.pow n.succ, _⟩,
  rw @spectrum.map_pow_of_pos ℂ _ _ _ _ _ a _ n.succ_pos,
  rintro _ ⟨x, hx, rfl⟩,
  obtain ⟨x, rfl⟩ := ha.spectrum_nonneg hx,
  refine ⟨x ^ n.succ, _⟩,
  simp only [complex.of_real_pow, eq_self_iff_true, coe_coe, nnreal.coe_pow],
end

@[simp]
lemma _root_.is_self_adjoint.subsingleton {R : Type*} [subsingleton R] [has_star R] (r : R) :
  is_self_adjoint r :=
subsingleton.elim _ _

-- please generalize
@[simp]
protected lemma subsingleton [subsingleton A] (a : A) : is_positive a :=
⟨is_self_adjoint.subsingleton a, by simp only [spectrum.of_subsingleton a, set.empty_subset]⟩

lemma spectrum_subset_Icc {a : A} (ha : is_positive a) : spectrum ℂ a ⊆ set.Icc (0 : ℂ) (‖a‖) :=
calc spectrum ℂ a ⊆ set.Icc (-‖a‖) (‖a‖) ∩ set.Ici (0 : ℂ)
    : set.subset_inter (ha.is_self_adjoint.spectrum_subset_Icc)
        (complex.Ici_zero_eq_range_coe.symm ▸ ha.spectrum_nonneg)
... ⊆ set.Icc (0 : ℂ) (‖a‖) : λ z hz, ⟨hz.2, hz.1.2⟩

lemma norm_mem_spectrum [nontrivial A] {a : A} (ha : is_positive a) : (‖a‖ : ℂ) ∈ spectrum ℂ a :=
begin
  obtain ⟨z, hz₁, hz₂⟩ := spectrum.exists_nnnorm_eq_spectral_radius a,
  obtain ⟨x, rfl⟩ := ha.spectrum_nonneg hz₁,
  rw [ha.is_self_adjoint.spectral_radius_eq_nnnorm, ennreal.coe_eq_coe] at hz₂,
  replace hz₂ := congr_arg (coe : _ → ℝ) hz₂,
  rw [coe_nnnorm, coe_nnnorm, coe_coe, is_R_or_C.norm_of_nonneg x.prop] at hz₂,
  rwa [coe_coe, hz₂] at hz₁,
end

end is_positive

end positive

section cfc_sa

open_locale complex_order
variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]

namespace self_adjoint

-- do we want to allow this even for `a` normal? It would be a bit weird.
-- I don't think so, because then we would have to provide the `is_star_normal` instance manually
noncomputable def cfc (a : self_adjoint A) : C(ℝ, ℝ) →⋆ₐ[ℝ] A :=
((cfc_star_alg_hom₂_real (a : A)).restrict_scalars ℝ).comp $
  continuous_map.complex_re.comp_star_alg_hom' ℝ ℝ



.
lemma cfc_apply (a : self_adjoint A) (f : C(ℝ, ℝ)) :
  (cfc a) f = (cfc_star_alg_hom₂_real ↑a) (f.comp continuous_map.complex_re) := rfl

lemma cfc_eq_of_eq_on {a : self_adjoint A} {f g : C(ℝ, ℝ)} (h : (spectrum ℝ (a : A)).eq_on f g) :
  cfc a f = cfc a g :=
cfc_star_alg_hom₂_eq_of_eq_on a (λ z hz, congr_arg coe (h $ a.prop.re_mem_spectrum hz))

--- need `cfc_eq_iff_eq_on`

lemma cfc_apply_is_self_adjoint (a : self_adjoint A) (f : C(ℝ, ℝ)) : is_self_adjoint (cfc a f) :=
show is_self_adjoint ((cfc_star_alg_hom₂_real (a : A)) (f.comp continuous_map.complex_re)),
  from cfc_star_alg_hom₂_real_is_self_adjoint (a : A) (f.comp continuous_map.complex_re)

lemma cfc_map_id (a : self_adjoint A) : cfc a (continuous_map.id ℝ) = a :=
cfc_star_alg_hom₂_map_id (a : A) ▸ cfc_star_alg_hom₂_eq_of_eq_on (a : A)
  (λ z hz, (a.prop.mem_spectrum_eq_re hz).symm)

lemma cfc_mem (a : self_adjoint A) (f : C(ℝ, ℝ)) : cfc a f ∈ C⋆((a : A)) :=
cfc_star_alg_hom_mem _

.

-- these lemmas can really be `↔`
lemma cfc_is_positive_of_nonneg (a : self_adjoint A) {f : C(ℝ, ℝ)}
  (hf : ∀ x ∈ spectrum ℝ (a : A), 0 ≤ f x) : is_positive (cfc a f) :=
begin
  rw [cfc_apply],
  exact is_positive.cfc_real_of_nonneg_on_spectrum (λ x hx, hf x.re $ a.prop.re_mem_spectrum hx),
end

/-- this is the square root of the positive part. It is the analogue of `real.sqrt`. -/
noncomputable def sqrt (a : self_adjoint A) : A := cfc a (continuous_map.mk real.sqrt)

lemma sq_sqrt (a : self_adjoint A) (ha : is_positive (a : A)) : (self_adjoint.sqrt a) ^ 2 = a :=
begin
  rw [sqrt, ←cfc_map_id a, ←map_pow],
  refine cfc_eq_of_eq_on (λ x hx, _),
  obtain ⟨x, rfl⟩ := ha.spectrum_real_nonneg hx,
  exact real.sq_sqrt x.prop,
end

-- again this is hard because we need a composition result
lemma sqrt_sq (a : self_adjoint A) : self_adjoint.sqrt (a ^ 2) = a :=
sorry

lemma _root_.is_positive_tfae (a : A) :
  tfae [is_positive a, ∃ x : self_adjoint A, a = x ^ 2, ∃ x : A, a = star x * x] :=
begin
  tfae_have : 1 → 2,
  { refine λ ha, _,
    set a' : self_adjoint A := ⟨a, ha.is_self_adjoint⟩,
    exact ⟨⟨self_adjoint.sqrt a', cfc_apply_is_self_adjoint a' _⟩, (sq_sqrt a' ha).symm⟩ },
  tfae_have : 2 → 3,
  { rintro ⟨x, hx⟩,
    refine ⟨(x : A), by rwa [x.prop.star_eq, ←sq]⟩ },
  tfae_have : 3 → 1,
  { rintro ⟨x, hx⟩,
    nontriviality A,
    have ha' : is_self_adjoint a := hx.symm ▸ is_self_adjoint.star_mul_self x,
    letI := ha'.is_star_normal,
    have ha : a⁺ - a⁻ = a, rw [pos_part_sub_neg_part, ha'.coe_real_part],
    have hxa : -(star (x * a⁻) * (x * a⁻)) = a⁻ ^ 3,
    { rw [star_mul, (is_positive.neg_part_is_positive a).is_self_adjoint.star_eq, mul_assoc,
        ←mul_assoc _ x, ←hx],
      nth_rewrite 1 ←ha'.coe_real_part,
      rw [←pos_part_sub_neg_part, sub_mul, pos_part_mul_neg_part, zero_sub, mul_neg, neg_neg],
      simp only [pow_succ, pow_one] },
    have hxa' : x * a⁻ = 0, from is_positive.eq_zero_of_is_positive_neg_star_mul_self
      (hxa.symm ▸ (is_positive.neg_part_is_positive a).pow 3),
    replace hxa := congr_arg (spectrum ℂ) hxa,
    simp only [hxa', mul_zero, neg_zero, spectrum.zero_eq, spectrum.map_pow] at hxa,
    have : spectrum ℂ (a⁻) ⊆ {0},
    { refine λ z hz, set.mem_singleton_iff.2 (@pow_eq_zero _ _ _ _ 3 _),
      exact set.mem_singleton_iff.1 (hxa.symm ▸ ⟨z, hz, rfl⟩), },
    letI := (is_positive.neg_part_is_positive a).is_star_normal,
    have : a⁻ = 0 := is_positive.eq_zero_of_spectrum_subset this,
    rw [this, sub_zero] at ha,
    exact ha ▸ is_positive.pos_part_is_positive a },
  tfae_finish
end

variables (A)

@[reducible]
def cstar_algebra.partial_order : partial_order A :=
{ le := λ a b, is_positive (b - a),
  le_refl := λ a, show is_positive (a - a), from (sub_self a).symm ▸ is_positive.zero,
  le_trans := λ a b c h h', show is_positive (c - a), from sub_add_sub_cancel c b a ▸ h'.add h,
  le_antisymm := λ a b h h', sub_eq_zero.1
    (h'.eq_zero_of_is_positive_neg $ (neg_sub a b).symm ▸ h) }

@[reducible]
def cstar_algebra.star_ordered_ring [partial_order A]
  (h_le : ∀ {a b : A}, a ≤ b ↔ is_positive (b - a)) : star_ordered_ring A :=
{ star := star,
  add_le_add_left := λ a b h c, h_le.2 $ (add_sub_add_left_eq_sub b a c).symm ▸ h_le.1 h,
  nonneg_iff := λ a, h_le.trans $ (sub_zero a).symm ▸ list.tfae.out (is_positive_tfae a) 0 2,
  .. ‹star_ring A› }

end self_adjoint

end cfc_sa

section final

open_locale complex_order
variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [partial_order A] [star_ordered_ring A] [cstar_ring A] [star_module ℂ A]

namespace star_ordered_ring

lemma nonneg_iff_is_positive {x : A} : 0 ≤ x ↔ is_positive x :=
begin
  rw star_ordered_ring.nonneg_iff,
  exact (list.tfae.out (is_positive_tfae x) 0 2).symm,
end

lemma le_iff_is_positive_sub {x y : A} : x ≤ y ↔ is_positive (y - x) :=
by rw [←sub_nonneg, nonneg_iff_is_positive]

lemma add_le_add {a b c d : A} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
by { rw [le_iff_is_positive_sub] at *, exact (add_sub_add_comm b d a c).symm ▸ h₁.add h₂ }

end star_ordered_ring

lemma is_positive.le_algebra_map_norm_self {a : A} (ha : is_positive a) :
  a ≤ algebra_map ℂ A (‖a‖) :=
begin
  rw [star_ordered_ring.le_iff_is_positive_sub],
  refine ⟨(show is_self_adjoint (algebra_map ℝ A ‖a‖), from _).sub ha.is_self_adjoint, _⟩,
  { exact (algebra_map_star_comm ‖a‖).symm.trans (congr_arg (algebra_map ℝ A) (star_trivial ‖a‖)) },
  { rw [←spectrum.singleton_sub_eq, ←complex.Ici_zero_eq_range_coe],
    intros z hz,
    simp_rw [set.mem_sub, set.mem_singleton_iff] at hz,
    obtain ⟨_, z, rfl, hz, rfl⟩ := hz,
    replace hz := ha.spectrum_subset_Icc hz,
    exact sub_nonneg.2 hz.2 }
end

lemma is_positive.le_algebra_map_iff {a : A} (ha : is_positive a) {x : ℝ≥0} :
  a ≤ algebra_map ℂ A x ↔ ‖a‖ ≤ x :=
begin
  rw [star_ordered_ring.le_iff_is_positive_sub],
  refine ⟨λ hxa, _, λ hx, _⟩,
  { replace hxa := hxa.spectrum_nonneg,
    rw [←spectrum.singleton_sub_eq, ←complex.Ici_zero_eq_range_coe] at hxa,
    nontriviality A,
    specialize hxa ⟨(x : ℂ), (‖a‖ : ℂ), set.mem_singleton _, ha.norm_mem_spectrum, rfl⟩,
    exact complex.real_le_real.1 (sub_nonneg.1 hxa) },
  { refine ⟨(show is_self_adjoint (algebra_map ℝ A x), from _).sub ha.is_self_adjoint, _⟩,
    { exact (algebra_map_star_comm (x : ℝ)).symm.trans
        (congr_arg (algebra_map ℝ A) (star_trivial x)) },
    { rw [←spectrum.singleton_sub_eq, ←complex.Ici_zero_eq_range_coe],
      intros z hz,
      simp_rw [set.mem_sub, set.mem_singleton_iff] at hz,
      obtain ⟨_, z, rfl, hz, rfl⟩ := hz,
      replace hz := ha.spectrum_subset_Icc hz,
      exact sub_nonneg.2 (hz.2.trans $ complex.real_le_real.2 hx) } }
end

.

lemma is_positive.le_algebra_map_norm {a : A} (ha : is_positive a) :
  a ≤ algebra_map ℂ A (‖a‖) :=
ha.le_algebra_map_iff.2 (show ‖a‖ ≤ ↑‖a‖₊, from le_rfl)

lemma is_positive.le_algebra_map_nnnorm {a : A} (ha : is_positive a) :
  a ≤ algebra_map ℂ A (‖a‖₊) :=
ha.le_algebra_map_norm

lemma norm_le_norm {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : ‖a‖ ≤ ‖b‖ :=
begin
  have hb := ha.trans hab,
  rw [star_ordered_ring.nonneg_iff_is_positive] at ha hb,
  simpa only [ha.le_algebra_map_iff] using hab.trans hb.le_algebra_map_nnnorm,
end


instance {R A : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R] [comm_ring A]
  [star_ring A] [algebra R A] [star_module R A] :
  algebra R (self_adjoint A) :=
{ to_fun := subtype.coind (algebra_map R A) $
    λ r, by simpa only [star_trivial] using (algebra_map_star_comm r).symm,
  map_one' := subtype.ext $ map_one (algebra_map R A),
  map_mul' := λ r s, subtype.ext $ map_mul (algebra_map R A) r s,
  map_zero' := subtype.ext $ map_zero (algebra_map R A),
  map_add' := λ r s, subtype.ext $ map_add (algebra_map R A) r s,
  commutes' := λ r x, subtype.ext $ algebra.commutes r (x : A),
  smul_def' := λ r x, subtype.ext $ algebra.smul_def r (x : A),
  .. self_adjoint.module }

.
instance {R : Type*} [add_group R] [star_add_monoid R] : has_star (self_adjoint R) :=
{ star := subtype.map star (λ r hr, congr_arg star hr) }

instance {R : Type*} [add_group R] [star_add_monoid R] : has_trivial_star (self_adjoint R) :=
{ star_trivial := λ r, subtype.ext r.prop }

.

open_locale complex_star_module

@[simps]
noncomputable def foo (X : Type*) [topological_space X] [compact_space X] :
  C(X, ℝ) ≃⋆ₐ[ℝ] self_adjoint C(X, ℂ) :=
{ to_fun := λ f, subtype.mk (continuous_map.comp_star_alg_hom X star_alg_hom.real_complex (algebra_map_clm ℝ ℂ).continuous f) (map_star _ _).symm,
  map_add' := λ f g, subtype.ext (by simpa only [map_add]),
  map_mul' := λ f g, subtype.ext (by simpa only [map_mul]),
  --commutes' := λ r, subtype.ext $ alg_hom_class.commutes (cfc_ℝ X) r,
  map_smul' := λ r f, subtype.ext (by simpa only [map_smul]),
  map_star' := λ f, subtype.ext (by simpa only [map_star]),
  inv_fun := λ f, (⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).comp ↑f,
  left_inv := λ f, continuous_map.ext $ λ x, by { simp only [subtype.coe_mk, continuous_map.comp_apply,
    star_alg_hom.real_complex_apply, algebra_map_clm_apply,
    complex.coe_algebra_map, continuous_map.coe_mk, complex.of_real_re], },
  --[subtype.coe_mk,
    --continuous_map.comp_apply, continuous_map.coe_mk, cfc_ℝ_apply_apply],
  right_inv := λ f, subtype.ext $ continuous_map.ext $ λ x,
    complex.eq_conj_iff_re.1 (fun_like.congr_fun f.prop x) }

.

lemma foo₁ (X : set ℂ) [compact_space X] :
  foo X ((⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).restrict X) =
  ℜ ((continuous_map.id ℂ).restrict X) :=
subtype.ext $ continuous_map.ext $ λ x,
  show (complex.re (x : ℂ) : ℂ) = (⅟(2 : ℝ) • ((x : ℂ) + (star x : ℂ))),
  by simp only [complex.re_eq_add_conj, inv_of_eq_inv, complex.real_smul, complex.of_real_inv,
    complex.of_real_bit0, complex.of_real_one, inv_mul_eq_div, is_R_or_C.star_def]

def star_alg_hom.self_adjoint {R A B : Type*} [comm_semiring R] [has_star R] [has_trivial_star R]
  [ring A] [star_ring A] [algebra R A] [star_module R A] [ring B] [star_ring B] [algebra R B]
  [star_module R B] (φ : A →⋆ₐ[R] B) : self_adjoint A →ₗ[R] self_adjoint B :=
{ to_fun := subtype.map φ (λ a ha, (map_star φ a ▸ congr_arg φ ha : star (φ a) = φ a)),
  map_add' := λ _ _, subtype.ext $ map_add φ _ _,
  map_smul' := λ _ _, subtype.ext $ map_smul φ _ _, }

lemma star_alg_hom.coe_self_adjoint {R A B : Type*} [comm_semiring R] [has_star R]
  [has_trivial_star R] [ring A] [star_ring A] [algebra R A] [star_module R A] [ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A →⋆ₐ[R] B) (a : self_adjoint A) :
  (φ.self_adjoint a : B) = φ a :=
rfl

lemma star_alg_hom.self_adjoint_map_real_part {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : (φ.restrict_scalars ℝ).self_adjoint (ℜ a) = ℜ (φ a) :=
subtype.ext $ show φ.restrict_scalars ℝ (⅟(2 : ℝ) • (a + star a)) = ⅟(2 : ℝ) • (φ a + star (φ a)),
  by { rw [map_smul, map_add, map_star], refl }

lemma star_alg_hom.map_real_part_coe {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : φ (ℜ a) = ℜ (φ a) :=
congr_arg coe (φ.self_adjoint_map_real_part a)

-- the definitional properties of `imaginary_part` are kind of abysmal.
lemma star_alg_hom.self_adjoint_map_imaginary_part {A B : Type*} [ring A] [star_ring A]
  [algebra ℂ A] [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B]
  (φ : A →⋆ₐ[ℂ] B) (a : A) : (φ.restrict_scalars ℝ).self_adjoint (ℑ a) = ℑ (φ a) :=
subtype.ext $
begin
  simp only [(φ.restrict_scalars ℝ).coe_self_adjoint, imaginary_part_apply_coe],
  rw [φ.restrict_scalars_apply ℝ, map_smul, ←φ.restrict_scalars_apply ℝ, map_smul, map_sub, map_star],
  refl,
end

lemma star_alg_hom.map_imaginary_part_coe {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : φ (ℑ a) = ℑ (φ a) :=
congr_arg coe (φ.self_adjoint_map_imaginary_part a)

def star_alg_hom.self_adjoint' {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A →⋆ₐ[R] B) : self_adjoint A →⋆ₐ[R] self_adjoint B :=
{ to_fun := φ.self_adjoint,
  map_one' := subtype.ext $ map_one φ,
  map_mul' := λ _ _, subtype.ext $ map_mul φ _ _,
  map_zero' := map_zero φ.self_adjoint,
  commutes' := λ _, subtype.ext $ alg_hom_class.commutes φ _,
  map_star' := λ _, subtype.ext $ map_star φ _,
  .. φ.self_adjoint }

def star_alg_equiv.self_adjoint {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A ≃⋆ₐ[R] B) : self_adjoint A ≃⋆ₐ[R] self_adjoint B :=
{ to_fun := (φ : A →⋆ₐ[R] B).self_adjoint',
  inv_fun := (φ.symm : B →⋆ₐ[R] A).self_adjoint',
  left_inv := λ a, subtype.ext $ φ.symm_apply_apply (a : A),
  right_inv := λ b, subtype.ext $ φ.apply_symm_apply (b : B),
  map_smul' := map_smul (φ : A →⋆ₐ[R] B).self_adjoint',
  .. (φ : A →⋆ₐ[R] B).self_adjoint', }

lemma star_alg_equiv.self_adjoint_coe_apply {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A ≃⋆ₐ[R] B) (a : self_adjoint A) :
  (φ.self_adjoint a : B) = φ (a : A) :=
rfl


-- `alg_equiv.trans` has argument order different than a lot of the other `equiv.trans`
.
noncomputable def cfc_to_self_adjoint (a : A) [is_star_normal a] :
  C(spectrum ℂ a, ℝ) ≃⋆ₐ[ℝ] self_adjoint C⋆(a) :=
(foo (spectrum ℂ a)).trans
  ((continuous_functional_calculus a).restrict_scalars ℝ).self_adjoint


end final


open_locale polynomial
open polynomial

lemma tmp : to_continuous_map_on_alg_hom (spectrum ℂ a) X = (continuous_map.id ℂ).restrict (spectrum ℂ a) :=
continuous_map.ext $ λ x, by simp only [to_continuous_map_on_alg_hom_apply,
  to_continuous_map_on_apply, to_continuous_map_apply, eval_X, continuous_map.coe_restrict,
  continuous_map.coe_id, function.comp.left_id]

lemma cfc_star_alg_hom_map_X :
  continuous_functional_calculus a (to_continuous_map_on_alg_hom (spectrum ℂ a) X) =
  ⟨a, self_mem_elemental_algebra ℂ a⟩ :=
by rw [tmp, continuous_functional_calculus_map_id]

lemma cfc_star_alg_hom_map_X_pow (n : ℕ) :
  (continuous_functional_calculus a (to_continuous_map_on_alg_hom (spectrum ℂ a) (X ^ n)) : A) = a ^ n :=
by simpa only [map_pow, cfc_star_alg_hom_map_X]

lemma cfc_star_alg_hom_sa_of_comp_real (f : C(spectrum ℂ a, ℝ)) :
  is_self_adjoint (↑ᶜᶠᶜ ((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).comp f)) :=
begin
  rw [is_self_adjoint, ←map_star],
  refine congr_arg _ (continuous_map.ext $ λ x, _),
  simp only [continuous_map.star_apply, continuous_map.comp_apply, continuous_map.coe_coe,
    algebra_map_clm_apply, complex.coe_algebra_map, is_R_or_C.star_def, is_R_or_C.conj_of_real],
end

lemma continous_map.comp_restrict {X Y Z : Type*} [topological_space X] [topological_space Y]
  [topological_space Z] (s : set X) (f : C(X, Y)) (g : C(Y, Z)) :
  (g.comp f).restrict s = g.comp (f.restrict s) :=
rfl

open_locale complex_star_module

lemma cfc_star_alg_hom_real_part :
  ↑ᶜᶠᶜ (continuous_map.restrict_star_alg_hom ℂ ℂ (spectrum ℂ a)
    ((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).comp (⟨complex.re, complex.continuous_re⟩))) = ℜ a :=
begin
  rw [real_part_apply_coe],
  simp only [←complex.coe_smul, complex.of_real_inv, complex.of_real_bit0, complex.of_real_one],
  conv_rhs { rw ←cfc_star_alg_hom_map_id a, },
  simp only [←map_add, ←map_star, ←map_smul],
  congr,
  ext1 x,
  show (x.re : ℂ) = 2⁻¹ * (x + star_ring_end ℂ x),
  rw [complex.re_eq_add_conj, inv_mul_eq_div],
end

/-
These are the things we want for normal elements. We probably don't need the first `↑`.

C(ℂ, ℂ) →[ℂ] C(σ ℂ a, ℂ) ≃[ℂ] C⋆(a) →[ℂ] A

  ↑[ℝ]            ↑[ℝ]

C(ℂ, ℝ) →[ℝ] C(σ ℂ a, ℝ)

-/

end cfc

.

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]

instance self_adjoint.is_star_normal (x : self_adjoint A) : is_star_normal (x : A) :=
x.prop.is_star_normal


/-namespace selfadjoint

noncomputable def cfc (a : self_adjoint A) : C(spectrum ℝ (a : A), ℂ) ≃⋆ₐ[ℂ] C⋆((a : A)) :=
(a.prop.homeo_spectrum_complex_real.comp_star_alg_equiv' ℂ ℂ).trans
  (star_subalgebra.continuous_functional_calculus a)

noncomputable def cfc' (a : self_adjoint A) :
  C(spectrum ℝ (a : A), ℂ) ≃⋆ₐ[ℂ] C(spectrum ℂ (a : A), ℂ) :=
a.prop.homeo_spectrum_complex_real.comp_star_alg_equiv' ℂ ℂ

.

noncomputable example : normed_algebra ℝ ℂ := @complex.normed_algebra ℝ _ (normed_algebra.id ℝ)
noncomputable example : module ℝ ℂ := module.complex_to_real ℂ
noncomputable example : module ℝ ℂ := @algebra.to_module _ _ _ _ (@complex.normed_algebra ℝ _ (normed_algebra.id ℝ)).to_algebra
example : module.complex_to_real ℂ = @algebra.to_module _ _ _ _ (@complex.normed_algebra ℝ _ (normed_algebra.id ℝ)).to_algebra := rfl
example : (@complex.normed_algebra ℝ _ (normed_algebra.id ℝ)).to_algebra = algebra.complex_to_real := rfl

lemma cfc'_map_id (a : self_adjoint A) :
  cfc' a (((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).comp (continuous_map.id ℝ)).restrict $ spectrum ℝ (a : A)) =
  (continuous_map.id ℂ).restrict (spectrum ℂ (a : A)) :=
continuous_map.ext $ λ x, show ((x : ℂ).re : ℂ) = x,
  from congr_arg coe (a.prop.mem_spectrum_eq_re x.prop).symm

lemma cfc'_map_id' (a : self_adjoint A) :
  cfc' a ((algebra_map_clm ℝ ℂ : C(ℝ, ℂ)).restrict $ spectrum ℝ (a : A)) =
  (continuous_map.id ℂ).restrict (spectrum ℂ (a : A)) :=
continuous_map.ext $ λ x, show ((x : ℂ).re : ℂ) = x,
  from congr_arg coe (a.prop.mem_spectrum_eq_re x.prop).symm
-- how can we relate these functional calculi?

end selfadjoint -/

.




noncomputable def cfc_ℝ (X : Type*) [topological_space X] : C(X, ℝ) →⋆ₐ[ℝ] C(X, ℂ) :=
continuous_map.comp_star_alg_hom X star_alg_hom.real_complex (algebra_map_clm ℝ ℂ).continuous

@[simp] lemma cfc_ℝ_apply_apply (X : Type*) [topological_space X] (f : C(X, ℝ)) (x : X) :
  cfc_ℝ X f x = star_alg_hom.real_complex (f x) := rfl

.
open star_subalgebra
-- this is not terribly useful because the image of this homomorphism doesn't even contain `a`,
-- unless `a` is selfadjoint.
/-
noncomputable def cfc_ℝ' (a : A) [is_star_normal a] : C(spectrum ℂ a, ℝ) →⋆ₐ[ℝ] C⋆(a) :=
((continuous_functional_calculus a).restrict_scalars ℝ : C(spectrum ℂ a, ℝ) →⋆ₐ[ℝ] C⋆(a)).comp
  (cfc_ℝ (spectrum ℂ a)) -/

.

instance {R A : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R] [comm_ring A]
  [star_ring A] [algebra R A] [star_module R A] :
  algebra R (self_adjoint A) :=
{ to_fun := subtype.coind (algebra_map R A) $
    λ r, by simpa only [star_trivial] using (algebra_map_star_comm r).symm,
  map_one' := subtype.ext $ map_one (algebra_map R A),
  map_mul' := λ r s, subtype.ext $ map_mul (algebra_map R A) r s,
  map_zero' := subtype.ext $ map_zero (algebra_map R A),
  map_add' := λ r s, subtype.ext $ map_add (algebra_map R A) r s,
  commutes' := λ r x, subtype.ext $ algebra.commutes r (x : A),
  smul_def' := λ r x, subtype.ext $ algebra.smul_def r (x : A),
  .. self_adjoint.module }

.
instance {R : Type*} [add_group R] [star_add_monoid R] : has_star (self_adjoint R) :=
{ star := subtype.map star (λ r hr, congr_arg star hr) }

instance {R : Type*} [add_group R] [star_add_monoid R] : has_trivial_star (self_adjoint R) :=
{ star_trivial := λ r, subtype.ext r.prop }

.

open_locale complex_star_module

@[simps]
noncomputable def foo (X : Type*) [topological_space X] [compact_space X] :
  C(X, ℝ) ≃⋆ₐ[ℝ] self_adjoint C(X, ℂ) :=
{ to_fun := λ f, subtype.mk (cfc_ℝ X f) (map_star _ _).symm,
  map_add' := λ f g, subtype.ext (by simpa only [map_add (cfc_ℝ X)]),
  map_mul' := λ f g, subtype.ext (by simpa only [map_mul (cfc_ℝ X)]),
  --commutes' := λ r, subtype.ext $ alg_hom_class.commutes (cfc_ℝ X) r,
  map_smul' := λ r f, subtype.ext (by simpa only [map_smul (cfc_ℝ X)]),
  map_star' := λ f, subtype.ext (by simpa only [map_star (cfc_ℝ X)]),
  inv_fun := λ f, (⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).comp ↑f,
  left_inv := λ f, continuous_map.ext $ λ x, by { simp only [subtype.coe_mk, continuous_map.comp_apply,
    cfc_ℝ_apply_apply, star_alg_hom.real_complex_apply, algebra_map_clm_apply,
    complex.coe_algebra_map, continuous_map.coe_mk, complex.of_real_re]},
  --[subtype.coe_mk,
    --continuous_map.comp_apply, continuous_map.coe_mk, cfc_ℝ_apply_apply],
  right_inv := λ f, subtype.ext $ continuous_map.ext $ λ x,
    complex.eq_conj_iff_re.1 (fun_like.congr_fun f.prop x) }

.

lemma foo₁ (X : set ℂ) [compact_space X] :
  foo X ((⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).restrict X) =
  ℜ ((continuous_map.id ℂ).restrict X) :=
subtype.ext $ continuous_map.ext $ λ x,
  show (complex.re (x : ℂ) : ℂ) = (⅟(2 : ℝ) • ((x : ℂ) + (star x : ℂ))),
  by simp only [complex.re_eq_add_conj, inv_of_eq_inv, complex.real_smul, complex.of_real_inv,
    complex.of_real_bit0, complex.of_real_one, inv_mul_eq_div, is_R_or_C.star_def]

def star_alg_hom.self_adjoint {R A B : Type*} [comm_semiring R] [has_star R] [has_trivial_star R]
  [ring A] [star_ring A] [algebra R A] [star_module R A] [ring B] [star_ring B] [algebra R B]
  [star_module R B] (φ : A →⋆ₐ[R] B) : self_adjoint A →ₗ[R] self_adjoint B :=
{ to_fun := subtype.map φ (λ a ha, (map_star φ a ▸ congr_arg φ ha : star (φ a) = φ a)),
  map_add' := λ _ _, subtype.ext $ map_add φ _ _,
  map_smul' := λ _ _, subtype.ext $ map_smul φ _ _, }

lemma star_alg_hom.coe_self_adjoint {R A B : Type*} [comm_semiring R] [has_star R]
  [has_trivial_star R] [ring A] [star_ring A] [algebra R A] [star_module R A] [ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A →⋆ₐ[R] B) (a : self_adjoint A) :
  (φ.self_adjoint a : B) = φ a :=
rfl

lemma star_alg_hom.self_adjoint_map_real_part {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : (φ.restrict_scalars ℝ).self_adjoint (ℜ a) = ℜ (φ a) :=
subtype.ext $ show φ.restrict_scalars ℝ (⅟(2 : ℝ) • (a + star a)) = ⅟(2 : ℝ) • (φ a + star (φ a)),
  by { rw [map_smul, map_add, map_star], refl }

lemma star_alg_hom.map_real_part_coe {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : φ (ℜ a) = ℜ (φ a) :=
congr_arg coe (φ.self_adjoint_map_real_part a)

-- the definitional properties of `imaginary_part` are kind of abysmal.
lemma star_alg_hom.self_adjoint_map_imaginary_part {A B : Type*} [ring A] [star_ring A]
  [algebra ℂ A] [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B]
  (φ : A →⋆ₐ[ℂ] B) (a : A) : (φ.restrict_scalars ℝ).self_adjoint (ℑ a) = ℑ (φ a) :=
subtype.ext $
begin
  simp only [(φ.restrict_scalars ℝ).coe_self_adjoint, imaginary_part_apply_coe],
  rw [φ.restrict_scalars_apply ℝ, map_smul, ←φ.restrict_scalars_apply ℝ, map_smul, map_sub, map_star],
  refl,
end

lemma star_alg_hom.map_imaginary_part_coe {A B : Type*} [ring A] [star_ring A] [algebra ℂ A]
  [star_module ℂ A] [ring B] [star_ring B] [algebra ℂ B] [star_module ℂ B] (φ : A →⋆ₐ[ℂ] B)
  (a : A) : φ (ℑ a) = ℑ (φ a) :=
congr_arg coe (φ.self_adjoint_map_imaginary_part a)

def star_alg_hom.self_adjoint' {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A →⋆ₐ[R] B) : self_adjoint A →⋆ₐ[R] self_adjoint B :=
{ to_fun := φ.self_adjoint,
  map_one' := subtype.ext $ map_one φ,
  map_mul' := λ _ _, subtype.ext $ map_mul φ _ _,
  map_zero' := map_zero φ.self_adjoint,
  commutes' := λ _, subtype.ext $ alg_hom_class.commutes φ _,
  map_star' := λ _, subtype.ext $ map_star φ _,
  .. φ.self_adjoint }

def star_alg_equiv.self_adjoint {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A ≃⋆ₐ[R] B) : self_adjoint A ≃⋆ₐ[R] self_adjoint B :=
{ to_fun := (φ : A →⋆ₐ[R] B).self_adjoint',
  inv_fun := (φ.symm : B →⋆ₐ[R] A).self_adjoint',
  left_inv := λ a, subtype.ext $ φ.symm_apply_apply (a : A),
  right_inv := λ b, subtype.ext $ φ.apply_symm_apply (b : B),
  map_smul' := map_smul (φ : A →⋆ₐ[R] B).self_adjoint',
  .. (φ : A →⋆ₐ[R] B).self_adjoint', }

lemma star_alg_equiv.self_adjoint_coe_apply {R A B : Type*} [comm_semiring R] [star_ring R] [has_trivial_star R]
  [comm_ring A] [star_ring A] [algebra R A] [star_module R A] [comm_ring B] [star_ring B]
  [algebra R B] [star_module R B] (φ : A ≃⋆ₐ[R] B) (a : self_adjoint A) :
  (φ.self_adjoint a : B) = φ (a : A) :=
rfl


-- `alg_equiv.trans` has argument order different than a lot of the other `equiv.trans`
.
noncomputable def cfc_to_self_adjoint (a : A) [is_star_normal a] :
  C(spectrum ℂ a, ℝ) ≃⋆ₐ[ℝ] self_adjoint C⋆(a) :=
(foo (spectrum ℂ a)).trans
  ((continuous_functional_calculus a).restrict_scalars ℝ).self_adjoint

.
lemma coe_cfc_to_self_adjoint_apply (a : A) [is_star_normal a] (f : C(spectrum ℂ a, ℂ)) :
  (cfc_to_self_adjoint a : C(spectrum ℂ a, ℝ) → self_adjoint C⋆(a))
  ((⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).comp f) =
  ℜ (continuous_functional_calculus a f) :=
begin
  refine subtype.ext (subtype.ext _),
  simp only [cfc_to_self_adjoint, real_part_apply_coe],
  simp only [←complex.coe_smul, complex.of_real_inv, complex.of_real_bit0, complex.of_real_one],
  simp only [←map_star, ←map_add, ←map_smul, star_alg_equiv.trans_apply,
    star_alg_equiv.self_adjoint_coe_apply, star_alg_equiv.restrict_scalars_apply],
  congr,
  ext1 x,
  simp only [foo_apply_coe, cfc_ℝ_apply_apply, continuous_map.comp_apply,
    star_alg_hom.real_complex_apply, algebra_map_clm_coe, complex.coe_algebra_map,
    continuous_map.coe_mk, complex.re_eq_add_conj, ←inv_mul_eq_div],
  refl,
end

lemma cfc_to_self_adjoint_map_re (a : A) [is_star_normal a] :
  (cfc_to_self_adjoint a : C(spectrum ℂ a, ℝ) → self_adjoint C⋆(a))
  ((⟨complex.re, complex.continuous_re⟩ : C(ℂ, ℝ)).restrict $ spectrum ℂ a) =
  ℜ (⟨a, self_mem_elemental_algebra ℂ a⟩ : C⋆(a)) :=
begin
  convert coe_cfc_to_self_adjoint_apply a ((continuous_map.id ℂ).restrict $ spectrum ℂ a),
  exact (continuous_functional_calculus_map_id a).symm,
end

.

noncomputable def self_adjoint.cfc (a : self_adjoint A) :
  C(spectrum ℝ (a : A), ℝ) ≃⋆ₐ[ℝ] self_adjoint C⋆((a : A)) :=
(a.prop.homeo_spectrum_complex_real.comp_star_alg_equiv' ℝ ℝ).trans (cfc_to_self_adjoint (a : A))

lemma self_adjoint.cfc_map_id (a : self_adjoint A) :
  (self_adjoint.cfc a : C(spectrum ℝ (a : A), ℝ) → self_adjoint C⋆((a : A)))
  ((continuous_map.id ℝ).restrict (spectrum ℝ (a : A))) =
  ℜ (⟨(a : A), self_mem_elemental_algebra ℂ (a : A)⟩ : C⋆((a : A))) :=
cfc_to_self_adjoint_map_re a

.


lemma self_adjoint.is_unit_iff_is_unit_coe (a : self_adjoint A) (b : self_adjoint C⋆((a : A))) :
  is_unit b ↔ is_unit (b : C⋆((a : A))) :=
begin
  split,
  intros hb,
  refine ⟨⟨(b : C⋆((a : A))), ↑(↑hb.unit⁻¹ : self_adjoint C⋆((a : A))), _, _⟩, rfl⟩,
  { rw [←self_adjoint.coe_mul, is_unit.mul_coe_inv, self_adjoint.coe_one] },
  { rw [←self_adjoint.coe_mul, is_unit.coe_inv_mul, self_adjoint.coe_one] },
  intros hb,
  let binv : self_adjoint C⋆((a : A)) :=
    ⟨↑hb.unit⁻¹, by { rw [self_adjoint.mem_iff, ←units.coe_star_inv], congr', ext,
      rw [units.coe_star, is_unit.unit_spec, b.prop.star_eq], }⟩,
  refine ⟨⟨b, binv, subtype.ext hb.mul_coe_inv, subtype.ext hb.coe_inv_mul⟩, rfl⟩,
end

lemma self_adjoint.cfc_spectral_mapping_aux (a : self_adjoint A) (b : self_adjoint C⋆((a : A))) :
  spectrum ℝ b = spectrum ℝ (b : C⋆((a : A))) :=
begin
  ext x,
  simp only [spectrum.mem_iff, not_iff_not],
  exact self_adjoint.is_unit_iff_is_unit_coe a _,
end

lemma self_adjoint.cfc_spectral_mapping (a : self_adjoint A) (f : C(spectrum ℝ (a : A), ℝ)) :
  spectrum ℝ ((self_adjoint.cfc a : C(spectrum ℝ (a : A), ℝ) → self_adjoint C⋆((a : A))) f : C⋆((a : A))) = set.range f :=
by rw [←self_adjoint.cfc_spectral_mapping_aux, alg_equiv.spectrum_eq,
  continuous_map.spectrum_eq_range]

.

/-lemma self_adjoint.coe_zero {R : Type*} [add_comm_group R] [star_add_monoid R] :
  ((0 : self_adjoint R) : R) = 0 := -/
noncomputable def self_adjoint.cfc_hom (a : self_adjoint A) : C(spectrum ℝ (a : A), ℝ) →⋆ₐ[ℝ] A :=
{ to_fun := λ f, (C⋆((a : A)).subtype.restrict_scalars ℝ)
    ((self_adjoint.cfc a : C(spectrum ℝ (a : A), ℝ) → self_adjoint C⋆((a : A))) f),
  map_one' := by rw [map_one, self_adjoint.coe_one, map_one],
  map_mul' := λ f g, by rw [map_mul, self_adjoint.coe_mul, map_mul],
  map_zero' := by rw [map_zero, add_subgroup.coe_zero, map_zero],
  map_add' := λ f g, by rw [map_add, add_subgroup.coe_add, map_add],
  commutes' := λ r, by { rw [alg_hom_class.commutes], refl, },
  map_star' := λ f,
  begin
    rw [star_trivial],
    have := ((self_adjoint.cfc a : C(spectrum ℝ (a : A), ℝ) → self_adjoint C⋆((a : A))) f).prop.star_eq,
    rw ←map_star,
    exact congr_arg _ this.symm,
  end }

.

lemma self_adjoint.cfc_hom_map_id (a : self_adjoint A) :
  ((self_adjoint.cfc_hom a : C(spectrum ℝ (a : A), ℝ) → A)
  ((continuous_map.id ℝ).restrict (spectrum ℝ (a : A)))) = a :=
begin
  convert congr_arg (C⋆((a : A)).subtype.restrict_scalars ℝ)
    (congr_arg (coe : self_adjoint C⋆((a : A)) → C⋆((a : A))) (self_adjoint.cfc_map_id a)) using 1,
  rw [star_alg_hom.restrict_scalars_apply, C⋆((a : A)).subtype.map_real_part_coe],
  have : is_self_adjoint (⟨(a : A), self_mem_elemental_algebra ℂ a⟩ : C⋆((a : A))),
    from subtype.ext a.prop,
  exact (this.star_hom_apply C⋆((a : A)).subtype).coe_real_part.symm,
end
.

lemma self_adjoint.cfc_hom_apply_is_self_adjoint (a : self_adjoint A)
  (f : C(spectrum ℝ (a : A), ℝ)) : is_self_adjoint (self_adjoint.cfc_hom a f) :=
show star (self_adjoint.cfc_hom a f) = self_adjoint.cfc_hom a f,
  from map_star (self_adjoint.cfc_hom a) f ▸ congr_arg (self_adjoint.cfc_hom a) (star_trivial f)

.

lemma self_adjoint.cfc_hom_spectral_mapping (a : self_adjoint A) (f : C(spectrum ℝ (a : A), ℝ)) :
  spectrum ℝ (self_adjoint.cfc_hom a f) = set.range f :=
begin
  show spectrum ℝ (((self_adjoint.cfc a : C(spectrum ℝ (a : A), ℝ) → self_adjoint C⋆((a : A))) f : C⋆((a : A))) : A) = set.range f,
  rw [spectrum.real_eq_preimage_coe_complex,
    ←star_subalgebra.spectrum_eq (star_subalgebra.elemental_algebra_closed (a : A)),
    ←spectrum.real_eq_preimage_coe_complex, self_adjoint.cfc_spectral_mapping],
end

.


#exit

structure is_positive (a : A) : Prop :=
(is_self_adjoint' : is_self_adjoint a)
(spectrum_nonneg' : coe '' spectrum ℝ≥0 a = spectrum ℂ a)

namespace is_positive

variables {a : A} (ha : is_positive a)

-- do we actually need this separate lemma?
protected lemma is_self_adjoint : is_self_adjoint a :=
ha.is_self_adjoint'

-- do we actually need this separate lemma?
lemma spectrum_nonneg : coe '' spectrum ℝ≥0 a = spectrum ℂ a :=
ha.spectrum_nonneg'

protected lemma is_star_normal : is_star_normal a := ha.is_self_adjoint.is_star_normal

lemma spectrum_to_nnreal {a : A} (ha : is_positive a) :
  real.to_nnreal '' spectrum ℝ a = spectrum ℝ≥0 a :=
begin
  rw [← ha.is_self_adjoint.spectrum_re, set.image_image, ←ha.spectrum_nonneg, set.image_image],
  simp only [coe_coe, complex.of_real_re, real.to_nnreal_coe, set.image_id'],
end

lemma star_normal_and_spectrum_nonneg_iff {a : A} :
  is_star_normal a ∧ coe '' spectrum ℝ≥0 a = spectrum ℂ a ↔ is_positive a :=
begin
  refine ⟨λ ha, _, λ ha, ⟨ha.is_star_normal, ha.spectrum_nonneg⟩⟩,
  { rcases ha with ⟨ha₁, ha₂⟩,
    refine ⟨is_self_adjoint.star_normal_and_spectrum_real_iff.1 ⟨ha₁, _⟩, ha₂⟩,
    refine set.ext (λ z, ⟨_, λ hz, _⟩),
    { rintro ⟨x, hx, rfl⟩, exact spectrum.mem_real_iff_complex.1 hx },
    { rw ←ha₂ at hz,
      rcases hz with ⟨x, hx, rfl⟩,
      exact ⟨(x : ℝ), spectrum.mem_nnreal_iff_real.1 hx, rfl⟩, } },
end

end is_positive


#exit
