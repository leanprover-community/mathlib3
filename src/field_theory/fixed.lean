/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.polynomial.group_ring_action
import field_theory.normal
import field_theory.separable
import field_theory.tower
import ring_theory.polynomial

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `finrank (fixed_points G F) F = fintype.card G`.

## Main Definitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of
`G`, where `G` is a group that acts on `F`.

-/

noncomputable theory
open_locale classical big_operators
open mul_action finset finite_dimensional

universes u v w

variables {M : Type u} [monoid M]
variables (G : Type u) [group G]
variables (F : Type v) [field F] [mul_semiring_action M F] [mul_semiring_action G F] (m : M)

/-- The subfield of F fixed by the field endomorphism `m`. -/
def fixed_by.subfield : subfield F :=
{ carrier := fixed_by M F m,
  zero_mem' := smul_zero m,
  add_mem' := λ x y hx hy, (smul_add m x y).trans $ congr_arg2 _ hx hy,
  neg_mem' := λ x hx, (smul_neg m x).trans $ congr_arg _ hx,
  one_mem' := smul_one m,
  mul_mem' := λ x y hx hy, (smul_mul' m x y).trans $ congr_arg2 _ hx hy,
  inv_mem' := λ x hx, (smul_inv' F m x).trans $ congr_arg _ hx }

section invariant_subfields

variables (M) {F}
/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class is_invariant_subfield (S : subfield F) : Prop :=
(smul_mem : ∀ (m : M) {x : F}, x ∈ S → m • x ∈ S)

variable (S : subfield F)

instance is_invariant_subfield.to_mul_semiring_action [is_invariant_subfield M S] :
  mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subfield.smul_mem m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

instance [is_invariant_subfield M S] : is_invariant_subring M (S.to_subring) :=
{ smul_mem := is_invariant_subfield.smul_mem }

end invariant_subfields

namespace fixed_points

variable (M)

-- we use `subfield.copy` so that the underlying set is `fixed_points M F`
/-- The subfield of fixed points by a monoid action. -/
def subfield : subfield F :=
subfield.copy (⨅ (m : M), fixed_by.subfield F m) (fixed_points M F)
(by { ext z, simp [fixed_points, fixed_by.subfield, infi, subfield.mem_Inf] })

instance : is_invariant_subfield M (fixed_points.subfield M F) :=
{ smul_mem := λ g x hx g', by rw [hx, hx] }


@[simp] theorem smul (m : M) (x : fixed_points.subfield M F) : m • x = x :=
subtype.eq $ x.2 m

-- Why is this so slow?
@[simp] theorem smul_polynomial (m : M) (p : polynomial (fixed_points.subfield M F)) : m • p = p :=
polynomial.induction_on p
  (λ x, by rw [polynomial.smul_C, smul])
  (λ p q ihp ihq, by rw [smul_add, ihp, ihq])
  (λ n x ih, by rw [smul_mul', polynomial.smul_C, smul, smul_pow, polynomial.smul_X])

instance : algebra (fixed_points.subfield M F) F :=
algebra.of_subring (fixed_points.subfield M F).to_subring

theorem coe_algebra_map :
  algebra_map (fixed_points.subfield M F) F = subfield.subtype (fixed_points.subfield M F) :=
rfl

lemma linear_independent_smul_of_linear_independent {s : finset F} :
  linear_independent (fixed_points.subfield G F) (λ i : (s : set F), (i : F)) →
  linear_independent F (λ i : (s : set F), mul_action.to_fun G F i) :=
begin
  haveI : is_empty ((∅ : finset F) : set F) := ⟨subtype.prop⟩,
  refine finset.induction_on s (λ _, linear_independent_empty_type)
    (λ a s has ih hs, _),
  rw coe_insert at hs ⊢,
  rw linear_independent_insert (mt mem_coe.1 has) at hs,
  rw linear_independent_insert' (mt mem_coe.1 has), refine ⟨ih hs.1, λ ha, _⟩,
  rw finsupp.mem_span_image_iff_total at ha, rcases ha with ⟨l, hl, hla⟩,
  rw [finsupp.total_apply_of_mem_supported F hl] at hla,
  suffices : ∀ i ∈ s, l i ∈ fixed_points.subfield G F,
  { replace hla := (sum_apply _ _ (λ i, l i • to_fun G F i)).symm.trans (congr_fun hla 1),
    simp_rw [pi.smul_apply, to_fun_apply, one_smul] at hla,
    refine hs.2 (hla ▸ submodule.sum_mem _ (λ c hcs, _)),
    change (⟨l c, this c hcs⟩ : fixed_points.subfield G F) • c ∈ _,
    exact submodule.smul_mem _ _ (submodule.subset_span $ mem_coe.2 hcs) },
  intros i his g,
  refine eq_of_sub_eq_zero (linear_independent_iff'.1 (ih hs.1) s.attach (λ i, g • l i - l i) _
    ⟨i, his⟩ (mem_attach _ _) : _),
  refine (@sum_attach _ _ s _ (λ i, (g • l i - l i) • (to_fun G F) i)).trans _, ext g', dsimp only,
  conv_lhs { rw sum_apply, congr, skip, funext, rw [pi.smul_apply, sub_smul, smul_eq_mul] },
  rw [sum_sub_distrib, pi.zero_apply, sub_eq_zero],
  conv_lhs { congr, skip, funext,
    rw [to_fun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← to_fun_apply _ x] },
  show ∑ x in s, g • (λ y, l y • to_fun G F y) x (g⁻¹ * g') =
    ∑ x in s, (λ y, l y • to_fun G F y) x g',
  rw [← smul_sum, ← sum_apply _ _ (λ y, l y • to_fun G F y),
      ← sum_apply _ _ (λ y, l y • to_fun G F y)], dsimp only,
  rw [hla, to_fun_apply, to_fun_apply, smul_smul, mul_inv_cancel_left]
end


variables [fintype G] (x : F)

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `fixed_points G F`. -/
def minpoly : polynomial (fixed_points.subfield G F) :=
(prod_X_sub_smul G F x).to_subring (fixed_points.subfield G F).to_subring $ λ c hc g,
let ⟨n, hc0, hn⟩ := polynomial.mem_frange_iff.1 hc in hn.symm ▸ prod_X_sub_smul.coeff G F x g n

namespace minpoly

theorem monic : (minpoly G F x).monic :=
by { simp only [minpoly, polynomial.monic_to_subring], exact prod_X_sub_smul.monic G F x }

theorem eval₂ : polynomial.eval₂ (subring.subtype $ (fixed_points.subfield G F).to_subring) x
  (minpoly G F x) = 0 :=
begin
  rw [← prod_X_sub_smul.eval G F x, polynomial.eval₂_eq_eval_map],
  simp only [minpoly, polynomial.map_to_subring],
end

theorem eval₂' :
  polynomial.eval₂ (subfield.subtype $ (fixed_points.subfield G F)) x (minpoly G F x) = 0 :=
eval₂ G F x

theorem ne_one :
  minpoly G F x ≠ (1 : polynomial (fixed_points.subfield G F)) :=
λ H, have _ := eval₂ G F x,
(one_ne_zero : (1 : F) ≠ 0) $ by rwa [H, polynomial.eval₂_one] at this

theorem of_eval₂ (f : polynomial (fixed_points.subfield G F))
  (hf : polynomial.eval₂ (subfield.subtype $ fixed_points.subfield G F) x f = 0) :
  minpoly G F x ∣ f :=
begin
  erw [← polynomial.map_dvd_map' (subfield.subtype $ fixed_points.subfield G F),
      minpoly, polynomial.map_to_subring _ (subfield G F).to_subring, prod_X_sub_smul],
  refine fintype.prod_dvd_of_coprime
    (polynomial.pairwise_coprime_X_sub $ mul_action.injective_of_quotient_stabilizer G x)
    (λ y, quotient_group.induction_on y $ λ g, _),
  rw [polynomial.dvd_iff_is_root, polynomial.is_root.def, mul_action.of_quotient_stabilizer_mk,
      polynomial.eval_smul',
      ← subfield.to_subring.subtype_eq_subtype,
      ← is_invariant_subring.coe_subtype_hom' G (fixed_points.subfield G F).to_subring,
      ← mul_semiring_action_hom.coe_polynomial, ← mul_semiring_action_hom.map_smul,
      smul_polynomial, mul_semiring_action_hom.coe_polynomial,
      is_invariant_subring.coe_subtype_hom', polynomial.eval_map,
      subfield.to_subring.subtype_eq_subtype, hf, smul_zero]
end

/- Why is this so slow? -/
theorem irreducible_aux (f g : polynomial (fixed_points.subfield G F))
  (hf : f.monic) (hg : g.monic) (hfg : f * g = minpoly G F x) :
  f = 1 ∨ g = 1 :=
begin
  have hf2 : f ∣ minpoly G F x,
  { rw ← hfg, exact dvd_mul_right _ _ },
  have hg2 : g ∣ minpoly G F x,
  { rw ← hfg, exact dvd_mul_left _ _ },
  have := eval₂ G F x,
  rw [← hfg, polynomial.eval₂_mul, mul_eq_zero] at this,
  cases this,
  { right,
    have hf3 : f = minpoly G F x,
    { exact polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 $ @of_eval₂ G _ F _ _ _  x f this) },
    rwa [← mul_one (minpoly G F x), hf3,
        mul_right_inj' (monic G F x).ne_zero] at hfg },
  { left,
    have hg3 : g = minpoly G F x,
    { exact polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 $ @of_eval₂ G _ F _ _ _  x g this) },
    rwa [← one_mul (minpoly G F x), hg3,
        mul_left_inj' (monic G F x).ne_zero] at hfg }
end

theorem irreducible : irreducible (minpoly G F x) :=
(polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

theorem is_integral : is_integral (fixed_points.subfield G F) x :=
⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

theorem minpoly_eq_minpoly :
  minpoly G F x = _root_.minpoly (fixed_points.subfield G F) x :=
minpoly.unique' (minpoly.irreducible G F x)
  (minpoly.eval₂ G F x) (minpoly.monic G F x)

instance normal : normal (fixed_points.subfield G F) F :=
⟨λ x, is_integral G F x, λ x, (polynomial.splits_id_iff_splits _).1 $
by { rw [← minpoly_eq_minpoly, minpoly,
    coe_algebra_map, ← subfield.to_subring.subtype_eq_subtype,
    polynomial.map_to_subring _ (fixed_points.subfield G F).to_subring, prod_X_sub_smul],
  exact polynomial.splits_prod _ (λ _ _, polynomial.splits_X_sub_C _) }⟩

instance separable : is_separable (fixed_points.subfield G F) F :=
⟨λ x, is_integral G F x,
 λ x, by {
  -- this was a plain rw when we were using unbundled subrings
  erw [← minpoly_eq_minpoly,
    ← polynomial.separable_map (fixed_points.subfield G F).subtype,
    minpoly, polynomial.map_to_subring _ ((subfield G F).to_subring) ],
  exact polynomial.separable_prod_X_sub_C_iff.2 (injective_of_quotient_stabilizer G x) }⟩

lemma dim_le_card : module.rank (fixed_points.subfield G F) F ≤ fintype.card G :=
begin
  refine dim_le (λ s hs, cardinal.nat_cast_le.1 _),
  rw [← @dim_fun' F G, ← cardinal.lift_nat_cast.{v (max u v)},
    cardinal.finset_card, ← cardinal.lift_id (module.rank F (G → F))],
  exact cardinal_lift_le_dim_of_linear_independent.{_ _ _ (max u v)}
    (linear_independent_smul_of_linear_independent G F hs)
end

instance : finite_dimensional (fixed_points.subfield G F) F :=
is_noetherian.iff_dim_lt_omega.2 $
lt_of_le_of_lt (dim_le_card G F) (cardinal.nat_lt_omega _)

lemma finrank_le_card : finrank (fixed_points.subfield G F) F ≤ fintype.card G :=
begin
  rw [← cardinal.nat_cast_le, finrank_eq_dim],
  apply dim_le_card,
end

end fixed_points

lemma linear_independent_to_linear_map (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [integral_domain A] [algebra R A] [integral_domain B] [algebra R B] :
  linear_independent B (alg_hom.to_linear_map : (A →ₐ[R] B) → (A →ₗ[R] B)) :=
have linear_independent B (linear_map.lto_fun R A B ∘ alg_hom.to_linear_map),
from ((linear_independent_monoid_hom A B).comp
  (coe : (A →ₐ[R] B) → (A →* B))
  (λ f g hfg, alg_hom.ext $ monoid_hom.ext_iff.1 hfg) : _),
this.of_comp _

lemma cardinal_mk_alg_hom (K : Type u) (V : Type v) (W : Type w)
  [field K] [field V] [algebra K V] [finite_dimensional K V]
            [field W] [algebra K W] [finite_dimensional K W] :
  cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
cardinal_mk_le_finrank_of_linear_independent $ linear_independent_to_linear_map K V W

noncomputable instance alg_hom.fintype (K : Type u) (V : Type v) (W : Type w)
  [field K] [field V] [algebra K V] [finite_dimensional K V]
            [field W] [algebra K W] [finite_dimensional K W] :
  fintype (V →ₐ[K] W) :=
classical.choice $ cardinal.lt_omega_iff_fintype.1 $
lt_of_le_of_lt (cardinal_mk_alg_hom K V W) (cardinal.nat_lt_omega _)

noncomputable instance alg_equiv.fintype (K : Type u) (V : Type v)
  [field K] [field V] [algebra K V] [finite_dimensional K V] :
  fintype (V ≃ₐ[K] V) :=
fintype.of_equiv (V →ₐ[K] V) (alg_equiv_equiv_alg_hom K V).symm

lemma finrank_alg_hom (K : Type u) (V : Type v)
  [field K] [field V] [algebra K V] [finite_dimensional K V] :
  fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
fintype_card_le_finrank_of_linear_independent $ linear_independent_to_linear_map K V V

namespace fixed_points
/-- Embedding produced from a faithful action. -/
@[simps apply {fully_applied := ff}]
def to_alg_hom (G : Type u) (F : Type v) [group G] [field F]
  [mul_semiring_action G F] [has_faithful_scalar G F] : G ↪ (F →ₐ[fixed_points.subfield G F] F) :=
{ to_fun := λ g, { commutes' := λ x, x.2 g,
    .. mul_semiring_action.to_ring_hom G F g },
  inj' := λ g₁ g₂ hg, to_ring_hom_injective G F $ ring_hom.ext $ λ x, alg_hom.ext_iff.1 hg x, }

lemma to_alg_hom_apply_apply {G : Type u} {F : Type v} [group G] [field F]
  [mul_semiring_action G F] [has_faithful_scalar G F] (g : G) (x : F) :
  to_alg_hom G F g x = g • x :=
rfl

theorem finrank_eq_card (G : Type u) (F : Type v) [group G] [field F]
  [fintype G] [mul_semiring_action G F] [has_faithful_scalar G F] :
  finrank (fixed_points.subfield G F) F = fintype.card G :=
le_antisymm (fixed_points.finrank_le_card G F) $
calc  fintype.card G
    ≤ fintype.card (F →ₐ[fixed_points.subfield G F] F) :
        fintype.card_le_of_injective _ (to_alg_hom G F).2
... ≤ finrank F (F →ₗ[fixed_points.subfield G F] F) : finrank_alg_hom (fixed_points G F) F
... = finrank (fixed_points.subfield G F) F : finrank_linear_map' _ _ _

theorem to_alg_hom_bijective (G : Type u) (F : Type v) [group G] [field F]
  [fintype G] [mul_semiring_action G F] [has_faithful_scalar G F] :
  function.bijective (to_alg_hom G F) :=
begin
  rw fintype.bijective_iff_injective_and_card,
  split,
  { exact (to_alg_hom G F).injective },
  { apply le_antisymm,
    { exact fintype.card_le_of_injective _ (to_alg_hom G F).injective },
    { rw ← finrank_eq_card G F,
      exact has_le.le.trans_eq (finrank_alg_hom _ F) (finrank_linear_map' _ _ _) } },
end

/-- Bijection between G and algebra homomorphisms that fix the fixed points -/
def to_alg_hom_equiv (G : Type u) (F : Type v) [group G] [field F]
  [fintype G] [mul_semiring_action G F] [has_faithful_scalar G F] :
    G ≃ (F →ₐ[fixed_points.subfield G F] F) :=
function.embedding.equiv_of_surjective (to_alg_hom G F) (to_alg_hom_bijective G F).2

end fixed_points
