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

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def splitting_field_aux_aux (n : ℕ) : Π {K : Type u} [field K], by exactI Π (f : K[X]),
  Σ (L : Type u) (inst : field L), by exactI algebra K L :=
nat.rec_on n (λ K inst f, ⟨K, inst, infer_instance⟩) (λ m ih K inst f,
  let L := ih (@remove_factor K inst f) in let h₁ := L.2.1 in let h₂ := L.2.2 in
  ⟨L.1, L.2.1, by
    { exactI (ring_hom.comp (algebra_map _ _) (adjoin_root.of f.factor)).to_algebra }⟩)

def splitting_field_aux (n : ℕ) {K : Type u} [field K] (f : K[X]) : Type u :=
  (splitting_field_aux_aux n f).1

instance splitting_field_aux.field (n : ℕ) {K : Type u} [field K] (f : K[X]) :
    field (splitting_field_aux n f) :=
  (splitting_field_aux_aux n f).2.1

instance splitting_field_aux.algebra (n : ℕ) {K : Type u} [field K] (f : K[X]) :
    algebra K (splitting_field_aux n f) :=
  (splitting_field_aux_aux n f).2.2

namespace splitting_field_aux

theorem succ (n : ℕ) (f : K[X]) :
  splitting_field_aux (n+1) f = splitting_field_aux n f.remove_factor := rfl

-- section lift_instances

-- /-! ### Instances on `splitting_field_aux`

-- In order to avoid diamond issues, we have to be careful to define each data field of algebraic
-- instances on `splitting_field_aux` by recursion, rather than defining the whole structure by
-- recursion at once.

-- The important detail is that the `smul` instances can be lifted _before_ we create the algebraic
-- instances; if we do not do this, this creates a mutual dependence on both on each other, and it
-- is impossible to untangle this mess. In order to do this, we need that these `smul` instances
-- are distributive in the sense of `distrib_smul`, which is weak enough to be guaranteed at this
-- stage. This is sufficient to lift an action to `adjoin_root f` (remember that this is a quotient,
-- so these conditions are equivalent to well-definedness), which is all we need.
-- -/

-- /-- Splitting fields have a zero. -/
-- protected def zero (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_zero.zero K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have an addition. -/
-- protected def add (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_add.add K _) (λ n ih K fK f, ih)

-- /-- Splitting fields inherit scalar multiplication. -/
-- protected def smul (n : ℕ) : Π (α : Type*) {K : Type u} [field K],
--   by exactI Π [distrib_smul α K],
--   by exactI Π [is_scalar_tower α K K] {f : K[X]},
--   α → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n
--   (λ α K fK ds ist f, by exactI @has_smul.smul _ K _)
--   (λ n ih α K fK ds ist f, by exactI ih α)

-- instance has_smul (α : Type*) (n : ℕ) {K : Type u} [field K] [distrib_smul α K]
--   [is_scalar_tower α K K] {f : K[X]} :
--   has_smul α (splitting_field_aux n f) :=
-- ⟨splitting_field_aux.smul n α⟩

-- instance is_scalar_tower (n : ℕ) : Π (R₁ R₂ : Type*) {K : Type u}
--   [has_smul R₁ R₂] [field K],
--   by exactI Π [distrib_smul R₂ K] [distrib_smul R₁ K],
--   by exactI Π [is_scalar_tower R₁ K K] [is_scalar_tower R₂ K K] [is_scalar_tower R₁ R₂ K]
--     {f : K[X]}, by exactI is_scalar_tower R₁ R₂ (splitting_field_aux n f) :=
-- nat.rec_on n (λ R₁ R₂ K _ _ hs₂ hs₁ _ _ h f,
-- begin
--   rcases hs₁ with @⟨@⟨⟨hs₁⟩,_⟩,_⟩,
--   rcases hs₂ with @⟨@⟨⟨hs₂⟩,_⟩,_⟩,
--   exact h,
-- end) $ λ n ih R₁ R₂ K _ _ _ _ _ _ _ f, by exactI ih R₁ R₂

-- /-- Splitting fields have a negation. -/
-- protected def neg (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_neg.neg K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have subtraction. -/
-- protected def sub (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_sub.sub K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have a one. -/
-- protected def one (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_one.one K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have a multiplication. -/
-- protected def mul (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_mul.mul K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have a power operation. -/
-- protected def npow (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   ℕ → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f n x, by exactI @has_pow.pow K _ _ x n) (λ n ih K fK f, ih)

-- /-- Splitting fields have an injection from the base field. -/
-- protected def mk (n : ℕ) : Π {K : Type u} [field K],
--   by exactI Π {f : K[X]}, K → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, id) (λ n ih K fK f, by exactI ih ∘ coe)
-- -- note that `coe` goes from `K → adjoin_root f`, and then `ih` lifts to the full splitting field
-- -- (as we generalise over all fields in this recursion!)

-- /-- Splitting fields have an inverse. -/
-- protected def inv (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_inv.inv K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have a division. -/
-- protected def div (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   splitting_field_aux n f → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f, by exactI @has_div.div K _) (λ n ih K fK f, ih)

-- /-- Splitting fields have powers by integers. -/
-- protected def zpow (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]},
--   ℤ → splitting_field_aux n f → splitting_field_aux n f :=
-- nat.rec_on n (λ K fK f n x, by exactI @has_pow.pow K _ _ x n) (λ n ih K fK f, ih)

-- -- I'm not sure why these two lemmas break, but inlining them seems to not work.
-- private lemma nsmul_zero (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]}
--   (x : splitting_field_aux n f), (0 : ℕ) • x = splitting_field_aux.zero n :=
-- nat.rec_on n (λ K fK f, by exactI zero_nsmul) (λ n ih K fK f, by exactI ih)

-- private lemma nsmul_succ (n : ℕ) : Π {K : Type u} [field K], by exactI Π {f : K[X]}
--   (k : ℕ) (x : splitting_field_aux n f),
--   (k + 1) • x = splitting_field_aux.add n x (k • x) :=
-- nat.rec_on n (λ K fK f n x, by exactI succ_nsmul x n) (λ n ih K fK f, by exactI ih)

-- instance field (n : ℕ) {K : Type u} [field K] {f : K[X]} :
--   field (splitting_field_aux n f) :=
-- begin
--   refine
--   { zero := splitting_field_aux.zero n,
--     one := splitting_field_aux.one n,
--     add := splitting_field_aux.add n,
--     zero_add := have h : _ := @zero_add, _,
--     add_zero := have h : _ := @add_zero, _,
--     add_assoc := have h : _ := @add_assoc, _,
--     add_comm := have h : _ := @add_comm, _,
--     neg := splitting_field_aux.neg n,
--     add_left_neg := have h : _ := @add_left_neg, _,
--     sub := splitting_field_aux.sub n,
--     sub_eq_add_neg := have h : _ := @sub_eq_add_neg, _,
--     mul := splitting_field_aux.mul n,
--     one_mul := have h : _ := @one_mul, _,
--     mul_one := have h : _ := @mul_one, _,
--     mul_assoc := have h : _ := @mul_assoc, _,
--     left_distrib := have h : _ := @left_distrib, _,
--     right_distrib := have h : _ := @right_distrib, _,
--     mul_comm := have h : _ := @mul_comm, _,
--     inv := splitting_field_aux.inv n,
--     inv_zero := have h : _ := @inv_zero, _,
--     div := splitting_field_aux.div n,
--     div_eq_mul_inv := have h : _ := @div_eq_mul_inv, _,
--     mul_inv_cancel := have h : _ := @mul_inv_cancel, _,
--     exists_pair_ne := have h : _ := @exists_pair_ne, _,
--     nat_cast := splitting_field_aux.mk n ∘ (coe : ℕ → K),
--     nat_cast_zero := have h : _ := @comm_ring.nat_cast_zero, _,
--     nat_cast_succ := have h : _ := @comm_ring.nat_cast_succ, _,
--     nsmul := (•),
--     nsmul_zero' := nsmul_zero n,
--     nsmul_succ' := nsmul_succ n,
--     int_cast := splitting_field_aux.mk n ∘ (coe : ℤ → K),
--     int_cast_of_nat := have h : _ := @comm_ring.int_cast_of_nat, _,
--     int_cast_neg_succ_of_nat := have h : _ := @comm_ring.int_cast_neg_succ_of_nat, _,
--     zsmul := (•),
--     zsmul_zero' := have h : _ := @subtraction_comm_monoid.zsmul_zero', _,
--     zsmul_succ' := have h : _ := @subtraction_comm_monoid.zsmul_succ', _,
--     zsmul_neg' := have h : _ := @subtraction_comm_monoid.zsmul_neg', _,
--     rat_cast := splitting_field_aux.mk n ∘ (coe : ℚ → K),
--     rat_cast_mk := have h : _ := @field.rat_cast_mk, _,
--     qsmul := (•),
--     qsmul_eq_mul' := have h : _ := @field.qsmul_eq_mul', _,
--     npow := splitting_field_aux.npow n,
--     npow_zero' := have h : _ := @comm_ring.npow_zero', _,
--     npow_succ' := have h : _ := @comm_ring.npow_succ', _,
--     zpow := splitting_field_aux.zpow n,
--     zpow_zero' := have h : _ := @field.zpow_zero', _,
--     zpow_succ' := have h : _ := @field.zpow_succ', _,
--     zpow_neg' := have h : _ := @field.zpow_neg', _},
--   all_goals {
--     unfreezingI { induction n with n ih generalizing K },
--     { apply @h K },
--     { exact @ih _ _ _ } },
-- end

-- instance inhabited {n : ℕ} {f : K[X]} :
--   inhabited (splitting_field_aux n f) := ⟨37⟩

-- /-- The injection from the base field as a ring homomorphism. -/
-- @[simps] protected def mk_hom (n : ℕ) {K : Type u} [field K] {f : K[X]} :
--   K →+* splitting_field_aux n f :=
-- { to_fun := splitting_field_aux.mk n,
--   map_one' :=
--   begin
--     unfreezingI { induction n with k hk generalizing K },
--     { simp [splitting_field_aux.mk] },
--     exact hk
--   end,
--   map_mul' :=
--   begin
--     unfreezingI { induction n with k hk generalizing K },
--     { simp [splitting_field_aux.mk] },
--     intros x y,
--     change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) _) = _,
--     rw [map_mul],
--     exact hk _ _
--   end,
--   map_zero' :=
--   begin
--     unfreezingI { induction n with k hk generalizing K },
--     { simp [splitting_field_aux.mk] },
--     change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) 0) = _,
--     rw [map_zero, hk],
--   end,
--   map_add' :=
--   begin
--     unfreezingI { induction n with k hk generalizing K },
--     { simp [splitting_field_aux.mk] },
--     intros x y,
--     change (splitting_field_aux.mk k) ((adjoin_root.of f.factor) _) = _,
--     rw [map_add],
--     exact hk _ _
--   end }

-- instance algebra (n : ℕ) (R : Type*) {K : Type u} [comm_semiring R] [field K]
--   [algebra R K] {f : K[X]} : algebra R (splitting_field_aux n f) :=
-- { to_fun := (splitting_field_aux.mk_hom n).comp (algebra_map R K),
--   smul := (•),
--   smul_def' :=
--   begin
--     unfreezingI { induction n with k hk generalizing K },
--     { exact algebra.smul_def },
--     exact hk
--   end,
--   commutes' := λ a b, mul_comm _ _,
--   .. (splitting_field_aux.mk_hom n).comp (algebra_map R K) }

-- /-- Because `splitting_field_aux` is defined by recursion, we have to make sure all instances
-- on `splitting_field_aux` are defined by recursion within the fields. Otherwise, there will be
-- instance diamonds such as the following: -/
-- example (n : ℕ) {K : Type u} [field K] {f : K[X]} :
--     (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f)) =
--   @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _) :=
-- rfl

-- end lift_instances

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

-- instance scalar_tower {n : ℕ} {f : K[X]} :
--   is_scalar_tower K (adjoin_root f.factor) (splitting_field_aux (n + 1) f) :=
-- splitting_field_aux.scalar_tower'

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

-- theorem exists_lift (n : ℕ) : ∀ {K : Type u} [field K], by exactI
--   ∀ (f : K[X]) (hfn : f.nat_degree = n) {L : Type*} [field L], by exactI
--     ∀ (j : K →+* L) (hf : splits j f), ∃ k : splitting_field_aux n f →+* L,
--       k.comp (algebra_map _ _) = j :=
-- nat.rec_on n (λ K _ _ _ L _ j _, by exactI ⟨j, j.comp_id⟩) $ λ n ih K _ f hf L _ j hj, by exactI
-- have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hf, cases hf },
-- have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
-- let ⟨r, hr⟩ := exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj
--   (factor_dvd_of_nat_degree_ne_zero hndf))
--   (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1) in
-- have hmf0 : map (adjoin_root.of f.factor) f ≠ 0, from map_ne_zero hfn0,
-- have hsf : splits (adjoin_root.lift j r hr) f.remove_factor,
-- by { rw ← X_sub_C_mul_remove_factor _ hndf at hmf0, refine (splits_of_splits_mul _ hmf0 _).2,
--   rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map,
--     adjoin_root.lift_comp_of, splits_id_iff_splits] },
-- let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (adjoin_root.lift j r hr) hsf in
-- ⟨k, by rw [algebra_map_succ, ← ring_hom.comp_assoc, hk, adjoin_root.lift_comp_of]⟩

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

def of_mv_polynomial (f : K[X]) :
    mv_polynomial (f.root_set (splitting_field_aux f.nat_degree f)) K →ₐ[K]
    splitting_field_aux f.nat_degree f :=
  mv_polynomial.aeval (λ i, i.1)

theorem of_mv_polynomial_surjective (f : K[X]) : function.surjective (of_mv_polynomial f) :=
  sorry

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
by { delta splitting_field; apply_instance }

instance inhabited : inhabited (splitting_field f) :=
  ⟨37⟩

instance {S : Type*} [comm_semiring S] [distrib_smul S K] [is_scalar_tower S K K] :
  has_smul S (splitting_field f) :=
  submodule.quotient.has_smul' _

instance algebra' {R : Type*} [comm_semiring R] [algebra R K] : algebra R (splitting_field f) :=
by { delta splitting_field; apply_instance }

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
    --To be golfed
    apply e.injective,
    have : e a ≠ 0,
    { intro w',
      apply w,
      simp only [add_equiv_class.map_eq_zero_iff] at w',
      exact w' },
    rw [map_mul, map_one],
    change e a * e (e.symm (e a)⁻¹) = 1,
    simp only [alg_equiv.apply_symm_apply],
    rwa [mul_inv_cancel],
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

theorem adjoin_roots : algebra.adjoin K
    (↑(f.map (algebra_map K $ splitting_field f)).roots.to_finset : set (splitting_field f)) = ⊤ :=
  is_splitting_field.adjoin_root_set f.splitting_field f

theorem adjoin_root_set : algebra.adjoin K (f.root_set (splitting_field f)) = ⊤ :=
adjoin_roots f

end splitting_field

end splitting_field

namespace is_splitting_field

variables (K L) [algebra K L]

variables {K}

instance (f : K[X]) : _root_.finite_dimensional K f.splitting_field :=
finite_dimensional f.splitting_field f

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
