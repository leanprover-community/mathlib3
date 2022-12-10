/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_four

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables (X : Type*) [mul_one_class X] [topological_space X]
variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units (ℤ_[p])) R)
variables {c : ℕ} [fact (0 < d)]
variables [algebra ℚ R] [norm_one_class R]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat locally_constant

/-- Looking at the set of characteristic functions obtained from the clopen basis. -/
--abbreviation s : set (locally_constant (zmod d × ℤ_[p]) R) := set.image (char_fn)
--  (⨆ n : ℕ, set.range (clopen_from p d n))
abbreviation s : set (locally_constant (zmod d × ℤ_[p]) R) := ⨆ n : ℕ, set.range
  (λ (a : zmod (d * p^n)), char_fn R (is_clopen_clopen_from p d n a))

example {α β : Type*} {f g : α → β} : f = g ↔ ∀ (x :α), f x = g x := function.funext_iff

example {α β : Type*} {a c : α} {b d : β} : (a, b) = (c, d) ↔ a = c ∧ b = d := prod.ext_iff

/-
--this is where char_zero is needed, ie, 1 ≠ 0
--generalize!
lemma char_fn_one (x : zmod d × ℤ_[p]) {U : set (zmod d × ℤ_[p])} (hU : is_clopen U) :
  x ∈ U ↔ char_fn _ R hU x = (1 : R) :=
begin
  rw char_fn, simp only [locally_constant.coe_mk, subtype.val_eq_coe, ite_eq_left_iff],
  split, any_goals { intro h, },
  { contrapose, push_neg, intros, apply h, },
  { by_contra h',
    apply nat.cast_add_one_ne_zero 0,
    symmetry,
    convert h h', any_goals { apply_instance, }, rw nat.cast_zero, rw zero_add, },
end

--generalize!
lemma char_fn_inj {U V : set (zmod d × ℤ_[p])} (hU : is_clopen U) (hV : is_clopen V)
  (h : char_fn R hU = char_fn R hV) : U = V :=
begin
  ext,
  rw locally_constant.ext_iff at h, specialize h x,
  split,
  { intros h', apply (char_fn_one p d R _ _).2,
    { rw (char_fn_one p d R _ _).1 h' at h, rw h.symm, }, },
  { intros h', apply (char_fn_one p d R _ _).2,
    { rw (char_fn_one p d R _ _).1 h' at h, rw h, }, },
end -/

lemma clopen_basis'_clopen (U : clopen_basis' p d) : is_clopen U.val :=
begin
  obtain ⟨n, a, h⟩ := U.prop,
  rw subtype.val_eq_coe, rw h,
  apply is_clopen_clopen_from,
end

lemma mem_s (U : clopen_basis' p d) :
  (char_fn R (clopen_basis'_clopen p d U)) ∈ s p d R :=
begin
  delta s,
  rw set.supr_eq_Union,
  rw set.mem_Union,
  obtain ⟨n, a, hU⟩ := U.prop,
  use n,
  rw set.mem_range,
  refine ⟨a, _⟩, rw ←subtype.val_eq_coe at hU,
  congr,
  rw hU,
  /-refl,
  --tidy, exact a,
  rw set.mem_def, simp,
  rw set.supr_eq_Union,
  rw set.mem_Union,
  rw set.mem_image, refine ⟨U.val, _, rfl⟩,
  simp only [set.mem_Union, set.mem_range, set.supr_eq_Union],
  refine ⟨n, a, hU.symm⟩, -/
end

lemma mem_s' (x : s p d R) : ∃ (i : ℕ) (y : zmod (d * p ^ i)),
  char_fn R (is_clopen_clopen_from p d i y) = x :=
begin
  have := x.prop,
  delta s at this,
  simp only [set.mem_Union, set.mem_range, set.supr_eq_Union] at this,
  exact this,
end

/-- An equivalence between the clopen basis and the characteristic functions corresponding to it. -/
noncomputable def clopen_char_fn_equiv : clopen_basis' p d ≃ s p d R :=
{
  to_fun := λ U, ⟨(char_fn R (clopen_basis'_clopen p d U)), mem_s p d R U⟩,
  --⟨(char_fn U.val), mem_s p d R U⟩,
  inv_fun := λ f, begin have := f.prop, delta s at this, simp at this,
    set n := classical.some this,
    set a := classical.some (classical.some_spec this),
    have h := classical.some_spec (classical.some_spec this),
    constructor,
    swap, { exact clopen_from p d n a, },
    refine ⟨n, a, rfl⟩,
    /-obtain ⟨h1, h2⟩ := classical.some_spec this,
    simp only [set.mem_Union, set.mem_range, set.supr_eq_Union] at h1,
    obtain ⟨n, a, hU⟩ := h1,
    refine ⟨n, a, _⟩,
    convert hU.symm, simp only [set.mem_Union, set.mem_range, set.supr_eq_Union],-/ end,
  left_inv := begin
    refine function.left_inverse_iff_comp.mpr _, rw function.funext_iff,
    intro U, rw id, rw subtype.ext_iff_val,
    obtain h := mem_s p d R U,
    delta s at h,
    simp only [set.mem_Union, set.mem_range, set.supr_eq_Union] at h,
    set n := classical.some h with hn,
    set a := classical.some (classical.some_spec h) with ha,
    have h1 := classical.some_spec (classical.some_spec h),
    --rcases h with ⟨n, a, h⟩,
--    rw set.mem_image at h1, cases h1 with z hz, cases hz with h1 h2,
    --simp only [set.mem_Union, set.mem_range, function.comp_app, set.supr_eq_Union, subtype.coe_mk,
      --subtype.val_eq_coe] at h1,
    simp only [id.def, function.comp_app, subtype.coe_mk],
    --simp only [set.mem_Union, set.mem_range, set.supr_eq_Union, subtype.coe_mk],
    --have := classical.some_spec (classical.some_spec U.prop),
    apply char_fn_inj R (is_clopen_clopen_from p d _ _) (clopen_basis'_clopen p d U),
--    convert (function.injective.eq_iff (char_fn_inj p d R)).1 h2,
    convert h1,
    --funext,
    --simp only [set.mem_Union, set.mem_range, iff_self, set.supr_eq_Union],
  end,
  right_inv := begin
    refine function.right_inverse_iff_comp.mpr _, ext,
    simp only [id.def, function.comp_app, subtype.coe_mk, subtype.val_eq_coe], congr,
    have := classical.some_spec (classical.some_spec (mem_s' p d R x)),
    convert this,
    --convert (classical.some_spec x.prop).2,
    --simp only [set.mem_Union, set.mem_range, set.supr_eq_Union],
    end,
}

--DO NOT DELETE!
/-instance general_version (n m : ℕ) (h : n < m) (a : zmod (p^n)) :
  fintype (equi_class p d n m h a) := sorry-/

/-
--construct a map from `ℤ/dℤ × ℤ_p → clopen_basis' p d` ?
/-- For m > n, χ_(b,a,n) = ∑_{j, b_j = a mod p^n} χ_(b,b_j,m) -/
lemma sum_char_fn_dependent (m n : ℕ) (h : m > n) (a : zmod (p^n)) (b : zmod d) :
  @char_fn _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩) = ∑ x in set.to_finset (equi_class p d n m h a),
  char_fn _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d)) (proj_lim_preimage_clopen p d n x) ⟩) :=
sorry -/

/-
/-- For m > n, E_c(χ_(b,a,n)) = ∑_{j, b_j = a mod p^n} E_c(χ_(b,b_j,m)) -/
lemma sum_char_fn_dependent_Ec' (m n : ℕ) [fact (0 < n)] (h : m > n) (a : zmod (p^n)) (b : zmod d) (hc : c.gcd p = 1) :
  E_c p d hc n a = ∑ x in set.to_finset (equi_class p d n m h a), E_c p d hc m x :=
sorry

lemma seems_useless (x : s p d R) : (x : locally_constant (zmod d × ℤ_[p]) R) =
  char_fn ((clopen_char_fn_equiv p d R).inv_fun x) :=
begin
  sorry,
end -/

/-lemma guess (n : ℕ) : zmod (d * (p^n)) ≃+* zmod d × zmod (p^n) :=
begin
  sorry,
end-/

/-lemma clopen_char_fn (U : clopen_basis' p d) : char_fn R (clopen_basis'_clopen p d U) =
  @char_fn _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (coe (classical.some (classical.some_spec U.prop)) : zmod d))
      (proj_lim_preimage_clopen p d (classical.some U.prop) (classical.some (classical.some_spec U.prop))) ⟩) :=
begin
  rw (function.injective.eq_iff (char_fn_inj p d R)),
  exact classical.some_spec (classical.some_spec U.prop),
end-/

--lemma trial : locally_constant (zmod d × ℤ_[p]) R = submodule.span R (s p d R) := sorry

-- TODO Remove this lemma
lemma mem_nonempty' {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s := ⟨⟨x, h⟩⟩

/-lemma bernoulli_measure_nonempty' (hc : c.gcd p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc _) :=
begin
  refine mem_nonempty _,
  {
    --constructor, swap 3,
    suffices : submodule.span R (s p d R) →ₗ[R] R, sorry, -- why you no work
      refine linear_map_from_span R _ _ (s p d R) _ _,
      { intro χ,
        --have : ∃ U : (clopen_basis' p d), char_fn _ U.val = (χ : locally_constant (zmod d × ℤ_[p]) R),
        --construct a bijection between `clopen_basis' p d` and `char_fn`?
        --sorry,
        --set U := classical.some this with hU,
        set U := (clopen_char_fn_equiv p d R).inv_fun χ with hU,
        exact E_c p d hc (classical.some U.prop) (classical.some (classical.some_spec U.prop)), },
      rintros f h, -- f is a relation, taking v in s to a; h says that ∑ a_i v_i = 0, tpt ∑ a_i E_c(v_i) = 0
      --apply finsupp.induction_linear f,
      rw finsupp.total_apply at *,
      simp,
      convert_to ∑ l in finsupp.support f, f(l) * (E_c p d hc (classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop) (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun l).prop))) = 0,
      { rw finsupp.sum_of_support_subset,
        swap 4, exact f.support,
        simp, simp,
        { rintros i hi, rw zero_mul, }, },
      set n := ⨆ (l : finsupp.support f), classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop + 1 with hn,
--      set n := ⨆ (l : finsupp.support f), ((clopen_char_fn_equiv p d R).inv_fun l) with hn,
      rw finsupp.sum_of_support_subset at h,
      swap 4, exact f.support,
      swap, simp, swap, simp,
      conv_lhs at h { apply_congr, skip, rw seems_useless p d R x,
        rw clopen_char_fn _,
        rw [sum_char_fn_dependent p d R n (classical.some
          ((clopen_char_fn_equiv p d R).inv_fun x).prop) _ (coe (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun x).prop))) _], },

      /-apply finsupp.induction f, { simp, },
      { rintros χ a g hg nza rel_g_zero h, rw finsupp.total_apply at *,
        rw finsupp.sum_add_index at *,
        {  }, sorry, sorry, sorry, sorry, },-/

      rw finsupp.total_apply,
      apply submodule.span_induction (trial p d R f),
      set s := classical.some (what_to_do p d R f) with hs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set i := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hi,
      set j := classical.some (classical.some_spec (what_to_do p d R f)) with hj,
      have hs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      exact ∑ (k : s), (j k) •
      (E_c p d hc (classical.some (i k).prop) (classical.some (classical.some_spec (i k).prop))),
    { rintros f g,
      set fs := classical.some (what_to_do p d R f) with hfs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hfi,
      set fj := classical.some (classical.some_spec (what_to_do p d R f)) with hfj,
      have hfs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      set gs := classical.some (what_to_do p d R g) with hgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set gi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R g))) with hgi,
      set gj := classical.some (classical.some_spec (what_to_do p d R g)) with hgj,
      have hgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R g))),
      set fgs := classical.some (what_to_do p d R (f + g)) with hfgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fgi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))) with hfgi,
      set fgj := classical.some (classical.some_spec (what_to_do p d R (f + g))) with hfgj,
      have hfgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))),
      convert_to ∑ (k : fgs), (fgj k) •
      (E_c p d hc (classical.some (fgi k).prop) (classical.some (classical.some_spec (fgi k).prop)) : R) =
      ∑ (k : fs), (fj k) •
      (E_c p d hc (classical.some (fi k).prop) (classical.some (classical.some_spec (fi k).prop)) : R) +
      ∑ (k : gs), (gj k) •
      (E_c p d hc (classical.some (gi k).prop) (classical.some (classical.some_spec (gi k).prop))),
  sorry, },
    sorry, },
sorry,
end -/

/-instance (c : ℤ) (hc : c.gcd p = 1) : distribution' (ℤ_[p]) :=
{
  phi := (classical.choice (bernoulli_measure_nonempty p c hc)).val
} -/

/-lemma subspace_induces_locally_constant (U : set X) [hU : semimodule A (locally_constant ↥U A)]
  (f : locally_constant U A) :
  ∃ (g : locally_constant X A), f.to_fun = (set.restrict g.to_fun U) := sorry -/

--example {A B : Type*} [monoid A] [monoid B] : units (A × B) ≃ units A × units B :=

example {A B : Type*} {U : set (A × B)} : set A := (prod.fst)'' U

lemma comp_unop_op {α : Type*} : @opposite.unop α ∘ opposite.op = id :=
by { ext, simp, }

def inv_mul_hom {α : Type*} [topological_space α] [comm_monoid α] : units α →* α :=
{
  to_fun := λ u, (units.coe_hom α) u⁻¹,
  map_one' := by simp,
  map_mul' := λ x y, begin simp only [mul_inv_rev, units.coe_hom_apply, units.coe_mul],
    rw mul_comm, end,
}

def op_mul_hom (α : Type*) [topological_space α] [comm_monoid α] : α →* αᵐᵒᵖ :=
{ to_fun := λ a, mul_opposite.op a,
  map_one' := by simp,
  map_mul' := λ x y, by { simp, rw mul_comm, }, }

example {α β γ : Type*} {f : α → β} {g : α → γ} : α → α × α := λ a, (a, a)

/-example {α : Type*} [topological_space α] [comm_monoid α] {U : set (units α)} (hU : is_open U)
  (h : continuous (@units.inv α _)) : is_open ((embed_product α)'' U) :=
begin
  suffices : is_open_map (embed_product α),
  { apply this U hU, },
  { apply inducing.is_open_map,
    { constructor, rw units.topological_space, },
    { have f1 : (embed_product α) =
        ((units.coe_hom α).prod (monoid_hom.comp (op_mul_hom α) inv_mul_hom)), sorry,
      have f2 : (embed_product α).to_fun =
        (monoid_hom.prod_map (units.coe_hom α) (monoid_hom.comp (op_mul_hom α) inv_mul_hom))
          ∘ (λ a, (a, a)), sorry,
      change is_open (set.range (embed_product α).to_fun), rw f2,
      apply is_open_map.is_open_range, apply is_open_map.comp,
      { simp, apply is_open_map.prod,
        { rintros V hV, --have := h.is_open_preimage V hV,
          sorry, },
        { apply is_open_map.comp,
          { change is_open_map opposite.op, apply is_open_map.of_inverse,
            swap 4, exact opposite.unop,
            refine continuous_unop,
            sorry,
            sorry, },
          { change is_open_map units.inv,
            --apply is_open_map.of_nhds_le, rintros a V hV, simp at hV,
            rintros V hV,
            have := preimage_interior_subset_interior_preimage h,
            --swap, exact units.inv '' V,
            rw set.preimage_image_eq _ at this,
            { rw ←subset_interior_iff_open, rintros z hz, rw interior_eq_iff_open.2 hV at this,
              simp only [set.mem_image, units.inv_eq_coe_inv] at hz,

              rw mem_interior, by_contra, push_neg at h,  },
          sorry, }, }, },
      sorry, }, },

  rw is_open_induced_iff at hU,
  rcases hU with ⟨t, ot, ht⟩,
--  rw is_open_prod_iff,
  rw is_open_iff_forall_mem_open, rintros x hx, rw set.mem_image at hx,
  rcases hx with ⟨y, memy, hy⟩,
  sorry,
end -/

--example {α : Type*} [comm_monoid α] [topological_space α] {s : set (units α)} [hs : is_open s] :

example {α : Type*} [monoid α] [topological_space α] : continuous (@units.inv ℤ_[p] _) :=
begin
  convert_to continuous (coe ∘ units.has_inv.inv),
  apply continuous.comp,
  apply units.continuous_coe,
  exact continuous_inv,
end

/-lemma prod_subset_singleton {α : Type*} [monoid α] [topological_space α] {s : set (units α)}
  {u : set α} {v : set αᵒᵖ} {x : units α} (hx : x.val ∈ u)
  (h : set.prod u v ⊆ (embed_product α)'' s) : u = {x} ∧ v = {(opposite.op ∘ units.inv) x} :=
begin
  have h1 : (x.val, (opposite.op ∘ units.inv) x) ∈ set.prod u v, sorry,
  have h2 : (opposite.op ∘ units.inv) x ∈ v, sorry,
  split,
  { ext y, split, all_goals { rintros h', },
    { rw set.mem_singleton_iff,
      have : (y, (opposite.op ∘ units.inv) x) ∈ set.prod u v, sorry,
      specialize h this, rw set.mem_image at h, cases h with z hz, rw embed_product at hz,
      simp at hz, rcases hz with ⟨h3, h4, h5⟩, rw ←units.ext_iff at h5, rw ←h4, rw ←units.ext_iff,
      refine inv_inj.mp h5, },
    { rw set.mem_singleton_iff at h', rw h', convert hx, }, },
  { ext y, split, all_goals { rintros h', },
    { rw set.mem_singleton_iff,
      have : (x.val, y) ∈ set.prod u v, sorry,
      specialize h this, rw set.mem_image at h, cases h with z hz, rw embed_product at hz,
      simp at hz, rcases hz with ⟨h3, h4, h5⟩, rw ←h5, simp [h4], rw ←units.ext_iff at h4, rw h4, },
    { rw set.mem_singleton_iff at h', rw h', apply h2, }, },
end-/

/-example {α : Type*} [monoid α] [topological_space α] {U : set (units α)} (hU : is_open U) :
  is_open ((units.val)'' U) :=
begin
  convert_to is_open ⋃ (x : units α) (hx : x ∈ U), {x.val},
  sorry,
  { apply is_open_Union, rintros x, apply is_open_Union, rintros hx,
    rw is_open_induced_iff at hU, rcases hU with ⟨t, ht, hU⟩, rw is_open_prod_iff at ht,
    obtain ⟨u, v, hu, hv, memu, memv, h⟩ := ht x.val ((opposite.op ∘ units.inv) x) _,
    have := prod_subset_singleton memu h, },
end-/

lemma top_eq_if_cont_inv' {α : Type*} [topological_space α] [monoid α]
 (h : @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
  infer_instance (@units.inv α _)) :
  topological_space.induced (units.coe_hom α) infer_instance ≤ units.topological_space :=
begin
  rw units.topological_space, rw ←continuous_iff_le_induced,
  apply continuous.prod_mk,
  { convert continuous_induced_dom, },
  { change continuous (mul_opposite.op ∘ units.inv),
    apply continuous.comp,
    { apply mul_opposite.continuous_op, },
    { convert h, }, },
end

/-lemma top_eq_if_cont_inv {α : Type*} [topological_space α] [monoid α]
 (h : @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
  infer_instance (@units.inv α _)) :
  topological_space.induced (units.coe_hom α) infer_instance ≤ units.topological_space :=
begin
  rintros s hs, rw units.topological_space at hs,
  rw is_open_induced_iff' at *, rcases hs with ⟨t, ht, hs⟩, rw preimage_embed_prod' at hs,
  have : (topological_space.induced (units.coe_hom α) infer_instance).is_open
    (opposite.op ∘ units.inv ⁻¹' (prod.snd '' t)),
  { apply continuous.is_open_preimage,
    { apply continuous.comp,
      { apply continuous_op, },
      { apply h, }, },
    { apply is_open_map_snd, refine ht, }, },
  rw is_open_induced_iff' at this, rcases this with ⟨t', ht', hs'⟩,
  rw ←hs' at hs,
  change _ ∩ (units.val)⁻¹' t' = _ at hs,
  refine ⟨prod.fst '' t ∩ t', _, _⟩,
  { apply is_open.inter,
    { apply is_open_map_fst, refine ht, },
    { refine ht', }, },
  { rw ←hs, refine set.preimage_inter, },
end -/

lemma ball_mem_unit {x z : ℤ_[p]} (hx : is_unit x) {r : ℝ} (pos_r : 0 < r)
  (memz : z ∈ metric.ball x r) (le_one : r ≤ 1) : is_unit z :=
begin
  rw metric.mem_ball at memz, rw dist_eq_norm at memz,
  have f : z = z - x + x := eq_add_of_sub_eq rfl,
  rw is_unit_iff at *,
  rw ←hx, rw ←norm_neg x,
  apply norm_eq_of_norm_add_lt_right,
  rw norm_neg x,
  ring_nf,
  rw hx,
  apply gt_of_ge_of_gt le_one memz,
end

lemma inv_mem_inv_ball {x z : units ℤ_[p]} {r : ℝ} (r_pos : 0 < r) (h : r ≤ 1)
  (hz : z.val ∈ metric.ball x.val r) : z.inv ∈ metric.ball x.inv r :=
begin
  have f := ball_mem_unit p (units.is_unit _) r_pos hz h,
  rw mem_ball_iff_norm at *,
  suffices : ∥z.val * x.val∥ * ∥z.inv - x.inv∥ < r,
  { rw padic_int.norm_mul at this, change is_unit z.val at f, rw is_unit_iff.1 f at this,
    rw units.val_eq_coe at this,
    rw is_unit_iff.1 (units.is_unit x) at this, rw one_mul at this, rw one_mul at this,
    exact this, },
  { rw ←padic_int.norm_mul, rw mul_sub, rw mul_right_comm,
    rw mul_assoc _ x.val _, rw units.val_inv, rw units.val_inv,
    rw one_mul, rw mul_one, change ∥z.val - x.val∥ < r at hz, rw norm_sub_rev, exact hz, },
end

lemma cont_inv : @continuous _ _ (topological_space.induced (units.coe_hom ℤ_[p]) infer_instance)
  infer_instance (@units.inv ℤ_[p] _) :=
begin
  constructor, rintros s hs, rw is_open_iff_forall_mem_open,
  rintros x hx,rw set.mem_preimage at hx,
  rw metric.is_open_iff at hs,
  obtain ⟨r, r_pos, hs⟩ := hs _ hx,
  by_cases r ≤ 1,
  { refine ⟨(units.inv)⁻¹' metric.ball x.inv r, _, _, _⟩,
    { rintros z hz, rw set.mem_preimage at *, apply hs hz, },
    { rw is_open_induced_iff,
      refine ⟨metric.ball x.val r, _, _⟩,
      { exact metric.is_open_ball, },
      { ext z,
        rw set.mem_preimage, rw set.mem_preimage,
        split,
        all_goals { rintros hz, },
        { apply inv_mem_inv_ball p r_pos h,
          convert hz, },
        { repeat { rw units.inv_eq_coe_inv at hz, rw ←units.val_eq_coe at hz, },
          convert inv_mem_inv_ball p r_pos h hz, }, }, },
    { rw set.mem_preimage, apply metric.mem_ball_self r_pos, }, },
  { push_neg at h,
    refine ⟨(units.inv)⁻¹' metric.ball x.inv 1, _, _, _⟩,
    { rintros z hz, rw set.mem_preimage at *,
      apply hs (metric.ball_subset_ball (le_of_lt h) hz), },
    { rw is_open_induced_iff,
      refine ⟨metric.ball x.val 1, _, _⟩,
      { exact metric.is_open_ball, },
      { ext z,
        rw set.mem_preimage, rw set.mem_preimage,
        split,
        all_goals { rintros hz, },
        { apply inv_mem_inv_ball p (zero_lt_one) (rfl.ge),
          convert hz, },
        { repeat { rw units.inv_eq_coe_inv at hz, rw ←units.val_eq_coe at hz, },
          convert inv_mem_inv_ball p (zero_lt_one) (rfl.ge) hz, }, }, },
    { rw set.mem_preimage, apply metric.mem_ball_self (zero_lt_one), }, },
end

lemma top_eq_iff_cont_inv {α : Type*} [monoid α] [topological_space α] :
  topological_space.induced (units.coe_hom α) infer_instance = units.topological_space ↔
    @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
      infer_instance (@units.inv α _) :=
begin
  split, all_goals { rintro h, },
  { rw h,
    have h1 : prod.snd ∘ (units.embed_product α) = mul_opposite.op ∘ units.val ∘ units.has_inv.inv,
    { ext, rw units.embed_product,
      simp only [function.comp_app, units.val_eq_coe, monoid_hom.coe_mk], },
    have h2 : continuous (prod.snd ∘ (units.embed_product α)),
    { apply continuous.comp,
      { refine continuous_snd, },
      { refine continuous_induced_dom, }, },
    rw h1 at h2,
    convert_to continuous (units.val ∘ units.has_inv.inv),
    have h3 := continuous.comp (@mul_opposite.continuous_unop α _) h2,
    rw ←function.comp.assoc at h3, rw mul_opposite.unop_comp_op at h3,
    simp only [function.comp.left_id] at h3, exact h3, },
  { apply le_antisymm,
    { apply top_eq_if_cont_inv', apply h, },
    { rw ←continuous_iff_le_induced, apply units.continuous_coe, }, },
end

/-lemma preimage_embed_prod {α : Type*} [monoid α] {u : set α} {v : set αᵒᵖ} :
  (embed_product α)⁻¹' u.prod v = units.val⁻¹' u ∩ (opposite.op ∘ units.inv)⁻¹' v := sorry-/

/-example {a : ℤ_[p]} : is_unit a ↔ is_unit (to_zmod a) :=
begin
  split, all_goals { rintros h, },
  { exact to_zmod.is_unit_map h, },
  { rw is_unit_iff_exists_inv at *,
    cases h with b h,

    refine is_unit_iff_exists_inv.mpr _,
    sorry, },
end-/

lemma is_open_coe : is_open_map (coe : units ℤ_[p] → ℤ_[p]) :=
begin
  change is_open_map (@units.val ℤ_[p] _),
  rintros U hU,
--  have hU' := top_eq_if_cont_inv
  rw ←(top_eq_iff_cont_inv.2 _) at hU, -- need this!
  { rw is_open_induced_iff at hU,
    rcases hU with ⟨t, ht, htU⟩,
    rw is_open_iff_forall_mem_open, rintros x hx, simp only [set.mem_image, units.val_eq_coe] at hx,
    rcases hx with ⟨y, hy, hyx⟩,
    have memt : x ∈ t,
    { rw ←htU at hy,
      rw set.mem_preimage at hy, simp only [units.coe_hom_apply] at hy, rw hyx at hy, apply hy, },
    rw metric.is_open_iff at ht,
    specialize ht x memt,
    rcases ht with ⟨r, r_pos, ht⟩,
    have is_unit_x : is_unit x,
    { rw ←hyx, simp only [units.is_unit], },
    by_cases r ≤ 1,
    { refine ⟨metric.ball x r, _, _, _⟩,
      { rintros z hz, rw set.mem_image,
        suffices : is_unit z,
        { refine ⟨is_unit.unit this, _, _⟩,
          { rw ←htU, rw set.mem_preimage, apply ht, convert hz, },
          { simp only [units.val_eq_coe], exact is_unit.unit_spec this, }, },
        { apply ball_mem_unit p is_unit_x r_pos hz h, }, },
      { exact metric.is_open_ball, },
      { exact metric.mem_ball_self r_pos, }, },
    { refine ⟨metric.ball x 1, _, _, _⟩,
      { { rintros z hz, rw set.mem_image,
        suffices : is_unit z,
        { refine ⟨is_unit.unit this, _, _⟩,
          { rw ←htU, rw set.mem_preimage, apply ht,
            change z ∈ metric.ball x r,
            push_neg at h,
            apply metric.ball_subset_ball (le_of_lt h), apply hz, },
          { simp only [units.val_eq_coe], exact is_unit.unit_spec this, }, },
        { apply ball_mem_unit p is_unit_x zero_lt_one (by convert hz) (by simp only), }, }, },
      { exact metric.is_open_ball, },
      { apply metric.mem_ball_self zero_lt_one, }, }, },
  { apply cont_inv, },
end

lemma is_open_coe' : is_open_map (coe : units (zmod d) → zmod d) :=
begin
  refine inducing.is_open_map _ trivial,
  constructor, symmetry, convert top_eq_iff_cont_inv.2 _,
  convert continuous_of_discrete_topology, apply discrete_topology_induced,
  change function.injective coe, exact units.ext,
end

lemma is_closed_coe : is_closed (set.range (coe : units ℤ_[p] → ℤ_[p])) :=
begin
  have : set.range (coe : units ℤ_[p] → ℤ_[p]) = set.preimage norm {1},
  { ext x,
    have : x ∈ set.range (coe : units ℤ_[p] → ℤ_[p]) ↔ is_unit x,
    { rw set.mem_range, split, all_goals { rintros h, },
      { cases h with y h, rw ←h, exact units.is_unit y, },
      { refine ⟨is_unit.unit h, is_unit.unit_spec _⟩, }, },
    rw set.mem_preimage, rw set.mem_singleton_iff, rw ←is_unit_iff, rw this, },
  { rw this, refine continuous_iff_is_closed.mp _ {1} _,
    { exact continuous_norm, },
    { exact t1_space.t1 1, }, },
end

lemma emb_coe : embedding (coe : units ℤ_[p] → ℤ_[p]) :=
begin
  constructor,
  { constructor, symmetry, convert top_eq_iff_cont_inv.2 _, apply cont_inv, },
  { exact units.ext, },
end
