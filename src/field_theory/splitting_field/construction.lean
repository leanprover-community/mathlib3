/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import field_theory.normal

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `splitting_field_aux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `splitting_field` is defined to be a quotient of a
`mv_polynomial` ring by the kernel of the obvious map into `splitting_field_aux`. Because the
actual `splitting_field` will be a quotient of a `mv_polynomial` it has nice instances on it.

-/

noncomputable theory
open_locale classical big_operators polynomial

universes u v w

variables {F : Type u} {K : Type v} {L : Type w}

namespace polynomial

variables [field K] [field L] [field F]
open polynomial

section splitting_field

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
if H : ∃ g, irreducible g ∧ g ∣ f then classical.some H else X

lemma irreducible_factor (f : K[X]) : irreducible (factor f) :=
begin
  rw factor, split_ifs with H, { exact (classical.some_spec H).1 }, { exact irreducible_X }
end

/-- See note [fact non-instances]. -/
lemma fact_irreducible_factor (f : K[X]) : fact (irreducible (factor f)) :=
⟨irreducible_factor f⟩

local attribute [instance] fact_irreducible_factor

theorem factor_dvd_of_not_is_unit {f : K[X]} (hf1 : ¬is_unit f) : factor f ∣ f :=
begin
  by_cases hf2 : f = 0, { rw hf2, exact dvd_zero _ },
  rw [factor, dif_pos (wf_dvd_monoid.exists_irreducible_factor hf1 hf2)],
  exact (classical.some_spec $ wf_dvd_monoid.exists_irreducible_factor hf1 hf2).2
end

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : K[X]} (hf : f.nat_degree ≠ 0) :
  factor f ∣ f :=
factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : K[X]) : polynomial (adjoin_root $ factor f) :=
map (adjoin_root.of f.factor) f /ₘ (X - C (adjoin_root.root f.factor))

theorem X_sub_C_mul_remove_factor (f : K[X]) (hf : f.nat_degree ≠ 0) :
  (X - C (adjoin_root.root f.factor)) * f.remove_factor = map (adjoin_root.of f.factor) f :=
let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf in
mul_div_by_monic_eq_iff_is_root.2 $ by rw [is_root.def, eval_map, hg, eval₂_mul, ← hg,
    adjoin_root.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : K[X]) :
  f.remove_factor.nat_degree = f.nat_degree - 1 :=
by rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map,
       nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
def splitting_field_aux_aux (n : ℕ) : Π {K : Type u} [field K], by exactI Π (f : K[X]),
  Σ (L : Type u) (inst : field L), by exactI algebra K L :=
nat.rec_on n (λ K inst f, ⟨K, inst, infer_instance⟩) (λ m ih K inst f,
  let L := ih (@remove_factor K inst f) in let h₁ := L.2.1 in let h₂ := L.2.2 in
  ⟨L.1, L.2.1, by
    { exactI (ring_hom.comp (algebra_map _ _) (adjoin_root.of f.factor)).to_algebra }⟩)

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `splitting_field_aux_aux`.
-/
def splitting_field_aux (n : ℕ) {K : Type u} [field K] (f : K[X]) : Type u :=
  (splitting_field_aux_aux n f).1

instance splitting_field_aux.field (n : ℕ) {K : Type u} [field K] (f : K[X]) :
    field (splitting_field_aux n f) :=
  (splitting_field_aux_aux n f).2.1

instance  (n : ℕ) {K : Type u} [field K] (f : K[X]) : inhabited (splitting_field_aux n f) :=
⟨0⟩

instance splitting_field_aux.algebra (n : ℕ) {K : Type u} [field K] (f : K[X]) :
    algebra K (splitting_field_aux n f) :=
  (splitting_field_aux_aux n f).2.2

namespace splitting_field_aux

theorem succ (n : ℕ) (f : K[X]) :
  splitting_field_aux (n+1) f = splitting_field_aux n f.remove_factor := rfl

instance algebra''' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
splitting_field_aux.algebra n _

instance algebra' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor) (splitting_field_aux n.succ f) :=
splitting_field_aux.algebra'''

instance algebra'' {n : ℕ} {f : K[X]} :
  algebra K (splitting_field_aux n f.remove_factor) :=
ring_hom.to_algebra (ring_hom.comp (algebra_map _ _) (adjoin_root.of f.factor))

instance scalar_tower' {n : ℕ} {f : K[X]} :
  is_scalar_tower K (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
is_scalar_tower.of_algebra_map_eq (λ x, rfl)

theorem algebra_map_succ (n : ℕ) (f : K[X]) :
  by exact algebra_map K (splitting_field_aux (n+1) f) =
    (algebra_map (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor)).comp
      (adjoin_root.of f.factor) :=
rfl

protected theorem splits (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    splits (algebra_map K $ splitting_field_aux n f) f :=
nat.rec_on n (λ K _ _ hf, by exactI splits_of_degree_le_one _
  (le_trans degree_le_nat_degree $ hf.symm ▸ with_bot.coe_le_coe.2 zero_le_one)) $ λ n ih K _ f hf,
by { resetI, rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits,
    ← X_sub_C_mul_remove_factor f (λ h, by { rw h at hf, cases hf })],
exact splits_mul _ (splits_X_sub_C _) (ih _ (nat_degree_remove_factor' hf)) }

theorem adjoin_root_set (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    algebra.adjoin K (f.root_set (splitting_field_aux n f)) = ⊤ :=
nat.rec_on n (λ K _ f hf, by exactI algebra.eq_top_iff.2 (λ x, subalgebra.range_le _ ⟨x, rfl⟩)) $
λ n ih K _ f hfn, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hfn, cases hfn },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
have hmf0 : map (algebra_map K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0,
begin
  simp_rw root_set at ⊢ ih,
  rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf,
         polynomial.map_mul] at hmf0 ⊢,
  rw [roots_mul hmf0, polynomial.map_sub, map_X, map_C, roots_X_sub_C, multiset.to_finset_add,
      finset.coe_union, multiset.to_finset_singleton, finset.coe_singleton,
      algebra.adjoin_union_eq_adjoin_adjoin, ← set.image_singleton,
      algebra.adjoin_algebra_map K (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor),
      adjoin_root.adjoin_root_eq_top, algebra.map_top,
      is_scalar_tower.adjoin_range_to_alg_hom K (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor),
      ih _ (nat_degree_remove_factor' hfn), subalgebra.restrict_scalars_top]
end

instance (f : K[X]) : is_splitting_field K (splitting_field_aux f.nat_degree f) f :=
  ⟨splitting_field_aux.splits _ _ rfl, splitting_field_aux.adjoin_root_set _ _ rfl⟩

/-- The natural map from `mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f))`
to `splitting_field_aux f.nat_degree f` sendind a variable to the corresponding root. -/
def of_mv_polynomial (f : K[X]) :
    mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K →ₐ[K]
    splitting_field_aux f.nat_degree f :=
  mv_polynomial.aeval (λ i, i.1)

theorem of_mv_polynomial_surjective (f : K[X]) : function.surjective (of_mv_polynomial f) :=
begin
  suffices : alg_hom.range (of_mv_polynomial f) = ⊤,
  { rw [← set.range_iff_surjective]; rwa [set_like.ext'_iff] at this },
  rw [of_mv_polynomial, ← algebra.adjoin_range_eq_range_aeval K, eq_top_iff,
    ← adjoin_root_set _ _ rfl],
  exact algebra.adjoin_le (λ α hα, algebra.subset_adjoin ⟨⟨α, hα⟩, rfl⟩)
end

/-- The algebra isomorphism between the quotient of
`mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K` by the kernel of
`of_mv_polynomial f` and `splitting_field_aux f.nat_degree f`. It is used to transport all the
algebraic structures from the latter to `f.splitting_field`, that is defined as the former. -/
def alg_equiv_quotient_mv_polynomial (f : K[X]) :
    (mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K ⧸
      ring_hom.ker (of_mv_polynomial f).to_ring_hom) ≃ₐ[K]
    splitting_field_aux f.nat_degree f :=
  (ideal.quotient_ker_alg_equiv_of_surjective (of_mv_polynomial_surjective f) : _)

end splitting_field_aux

/-- A splitting field of a polynomial. -/
def splitting_field (f : K[X]) :=
mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K ⧸
    ring_hom.ker (splitting_field_aux.of_mv_polynomial f).to_ring_hom

namespace splitting_field

variables (f : K[X])

instance comm_ring : comm_ring (splitting_field f) :=
ideal.quotient.comm_ring _

instance inhabited : inhabited (splitting_field f) :=
  ⟨37⟩

instance {S : Type*} [distrib_smul S K] [is_scalar_tower S K K] :
  has_smul S (splitting_field f) :=
  submodule.quotient.has_smul' _

instance algebra : algebra K (splitting_field f) :=
ideal.quotient.algebra _

instance algebra' {R : Type*} [comm_semiring R] [algebra R K] : algebra R (splitting_field f) :=
ideal.quotient.algebra _

instance is_scalar_tower {R : Type*} [comm_semiring R] [algebra R K] :
  is_scalar_tower R K (splitting_field f) :=
ideal.quotient.is_scalar_tower _ _ _

/-- The algebra equivalence with `splitting_field_aux`,
which we will use to construct the field structure. -/
def alg_equiv_splitting_field_aux (f : K[X]) :
    splitting_field f ≃ₐ[K] splitting_field_aux f.nat_degree f :=
  splitting_field_aux.alg_equiv_quotient_mv_polynomial f

instance : field (splitting_field f) :=
let e := alg_equiv_splitting_field_aux f in
{ rat_cast := λ a, algebra_map K _ (a : K),
  inv := λ a, e.symm (e a)⁻¹,
  qsmul := (•),
  qsmul_eq_mul' := λ a x, quotient.induction_on' x (λ p, congr_arg quotient.mk'
  begin
    ext,
    simp only [mv_polynomial.algebra_map_eq, rat.smul_def, mv_polynomial.coeff_smul,
      mv_polynomial.coeff_C_mul],
  end),
  rat_cast_mk := λ a b h1 h2,
  begin
    apply e.injective,
    change e (algebra_map K _ _) = _,
    simp only [map_rat_cast, map_nat_cast, map_mul, map_int_cast, alg_equiv.commutes],
    change _ = e ↑a * e (e.symm (e b)⁻¹),
    rw [alg_equiv.apply_symm_apply],
    convert field.rat_cast_mk a b h1 h2,
    all_goals { simp },
  end,
  exists_pair_ne := ⟨e.symm 0, e.symm 1, λ w, zero_ne_one ((e.symm).injective w)⟩,
  mul_inv_cancel := λ a w,
  begin
    apply e.injective,
    rw [map_mul, map_one],
    change e a * e (e.symm (e a)⁻¹) = 1,
    rw [alg_equiv.apply_symm_apply, mul_inv_cancel],
    exact (λ w', w (by simpa only [add_equiv_class.map_eq_zero_iff] using w')),
  end,
  inv_zero :=
  begin
    change e.symm (e 0)⁻¹ = 0,
    simp
  end,
  ..splitting_field.comm_ring f }

instance [char_zero K] : char_zero (splitting_field f) :=
char_zero_of_injective_algebra_map ((algebra_map K _).injective)

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `splitting_field f`.
example : (add_comm_monoid.nat_module : module ℕ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl

example : (add_comm_group.int_module _ : module ℤ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl

example [char_zero K] : (splitting_field.algebra' f) = algebra_rat :=
rfl

example {q : ℚ[X]} : algebra_int (splitting_field q) = splitting_field.algebra' q := rfl

instance _root_.polynomial.is_splitting_field.splitting_field (f : K[X]) :
    is_splitting_field K (splitting_field f) f :=
  is_splitting_field.of_alg_equiv _ f (splitting_field_aux.alg_equiv_quotient_mv_polynomial f).symm

protected theorem splits : splits (algebra_map K (splitting_field f)) f :=
is_splitting_field.splits f.splitting_field f

variables [algebra K L] (hb : splits (algebra_map K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : splitting_field f →ₐ[K] L :=
is_splitting_field.lift f.splitting_field f hb

theorem adjoin_root_set : algebra.adjoin K (f.root_set (splitting_field f)) = ⊤ :=
polynomial.is_splitting_field.adjoin_root_set _ f

end splitting_field

end splitting_field

namespace is_splitting_field

variables (K L) [algebra K L]

variables {K}

instance (f : K[X]) : _root_.finite_dimensional K f.splitting_field :=
finite_dimensional f.splitting_field f

instance [fintype K] (f : K[X]) : fintype f.splitting_field :=
finite_dimensional.fintype_of_fintype K _

instance (f : K[X]) : no_zero_smul_divisors K f.splitting_field := infer_instance

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv (f : K[X]) [is_splitting_field K L f] : L ≃ₐ[K] splitting_field f :=
begin
  refine alg_equiv.of_bijective (lift L f $ splits (splitting_field f) f)
    ⟨ring_hom.injective (lift L f $ splits (splitting_field f) f).to_ring_hom, _⟩,
  haveI := finite_dimensional (splitting_field f) f,
  haveI := finite_dimensional L f,
  have : finite_dimensional.finrank K L = finite_dimensional.finrank K (splitting_field f) :=
  le_antisymm
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift L f $ splits (splitting_field f) f).to_linear_map, from
        ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)))
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift (splitting_field f) f $ splits L f).to_linear_map, from
        ring_hom.injective (lift (splitting_field f) f $ splits L f : f.splitting_field →+* L))),
  change function.surjective (lift L f $ splits (splitting_field f) f).to_linear_map,
  refine (linear_map.injective_iff_surjective_of_finrank_eq_finrank this).1 _,
  exact ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)
end

end is_splitting_field

end polynomial

section normal

instance [field F] (p : F[X]) : normal F p.splitting_field := normal.of_is_splitting_field p

end normal
