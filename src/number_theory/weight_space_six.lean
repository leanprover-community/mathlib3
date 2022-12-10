/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_five

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

noncomputable def ind_fn [has_zero A] (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :=
  λ x : (zmod d × ℤ_[p]), @dite _ (is_unit x.1 ∧ is_unit x.2)
    (classical.dec (is_unit x.fst ∧ is_unit x.snd)) (λ h, f (is_unit.unit h.1, is_unit.unit h.2)) (λ h, 0)

lemma ind_fn_eq_fun [has_zero A] (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  f.to_fun = (ind_fn A p d f) ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
begin
  ext x, rw function.comp, simp only, rw ind_fn, simp only,
  symmetry, convert dif_pos _,
  { rw prod.ext_iff, simp only [prod_map], split,
    all_goals { rw units.ext_iff,
      rw is_unit.unit_spec (units.is_unit _), }, },
  { simp only [units.is_unit, prod_map, and_self], },
end

noncomputable def loc_const_ind_fn [has_zero A] (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  locally_constant (zmod d × ℤ_[p]) A :=
{
  to_fun := ind_fn A p d f,
  is_locally_constant := begin
    haveI : ∀ (x : zmod d), decidable (is_unit x),
    { intro x,
      exact classical.dec (is_unit x), },
    haveI : ∀ (x : ℤ_[p]), decidable (is_unit x),
    { intro x,
      exact classical.dec (is_unit x), },
    have f4 : is_open_map (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])),
    { apply is_open_map.prod,
      { apply is_open_coe', },
      { apply is_open_coe, }, },
--    rw locally_constant.is_locally_constant,
    rintros s,
    have f1 := locally_constant.is_locally_constant f s,
    rw ind_fn_eq_fun at f1,
    rw set.preimage_comp at f1,
    by_cases (0 : A) ∈ s,
    { rw ←set.singleton_subset_iff at h,
      rw ←set.diff_union_of_subset h, rw set.preimage_union,
      apply is_open.union,
      { --copied same proof from below, how to reverse this? making new lemma required too many defs
        have f2 := locally_constant.is_locally_constant f (s \ {0}),
        rw ind_fn_eq_fun at f2,
        rw set.preimage_comp at f2,
        rw ←open_embedding.open_iff_preimage_open _ at f2,
        { exact f2, },
        { intros z hz,
          rw set.mem_preimage at hz,
          by_cases h' : is_unit z.1 ∧ is_unit z.2,
          { rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
            rw prod.ext_iff, simp only [prod.map_mk], split, all_goals { rw is_unit.unit_spec, }, },
          { have : ind_fn A p d f z = 0,
            { rw ind_fn, simp only, convert dif_neg h', },
            exfalso, rw this at hz,
            simp only [set.mem_singleton, set.mem_diff, not_true, and_false] at hz, apply hz, }, },
        { constructor,
          { apply embedding.prod_mk,
            { constructor,
              { constructor, symmetry, convert top_eq_iff_cont_inv.2 _,
                convert continuous_of_discrete_topology, apply discrete_topology_induced,
                change function.injective coe, exact units.ext, },
              { exact units.ext, }, },
            { apply emb_coe, }, },
          { apply is_open_map.is_open_range,
            exact f4, }, }, },
      { have f3 : (ind_fn A p d f)⁻¹' {0} = (prod.map (coe : units (zmod d) → zmod d)
          (coe : units ℤ_[p] → ℤ_[p]))''
          (f⁻¹' {0}) ∪ (set.range (prod.map (coe : units (zmod d) → zmod d)
            (coe : units ℤ_[p] → ℤ_[p])))ᶜ,
        { ext y, rw set.mem_union, rw set.mem_preimage, rw set.mem_singleton_iff, split,
          all_goals { rintros h', },
          { rw ind_fn at h',
            by_cases h'' : is_unit y.fst ∧ is_unit y.snd,
            { left, rw set.mem_image,
              refine ⟨(is_unit.unit h''.1, is_unit.unit h''.2), _, _⟩,
              { rw set.mem_preimage, rw set.mem_singleton_iff, rw ←h', symmetry, simp only,
                convert dif_pos h'', },
              { simp only [prod.map_mk], symmetry, rw prod.ext_iff, simp only, split,
                { rw is_unit.unit_spec h''.1, },
                { rw is_unit.unit_spec h''.2, }, }, },
            { right, contrapose h'', push_neg, rw ←set.mem_compl_iff at h'', rw compl_compl at h'',
              rw set.mem_range at h'', cases h'' with z hz, simp only [prod_map] at hz,
              rw prod.ext_iff at hz, simp only at hz, rw ←hz.1, rw ←hz.2,
              refine ⟨units.is_unit z.fst, units.is_unit z.snd⟩, }, },
          { rw ind_fn, simp only, cases h',
            { rw set.mem_image at h', cases h' with z hz, convert dif_pos _,
              swap, { rw ←hz.2, simp only [units.is_unit, prod_map, and_self], },
              { symmetry, rw set.mem_preimage at hz, rw set.mem_singleton_iff at hz,
                rw prod.ext_iff at hz, cases hz with h1 h2, convert h1,
                symmetry, rw prod.ext_iff, rw units.ext_iff, simp only [prod_map] at h2,
                simp only, rw units.ext_iff, split,
                { convert h2.1, },
                { convert h2.2, }, }, },
            { convert dif_neg _, rw set.mem_compl_iff at h', contrapose h', push_neg at h',
              push_neg, rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
              symmetry, rw prod.ext_iff, simp only [prod.map_mk], rw is_unit.unit_spec (h').1,
              rw is_unit.unit_spec (h').2, refine ⟨rfl, rfl⟩, }, }, },
        rw f3, apply is_open.union,
        { apply f4 _, apply locally_constant.is_locally_constant f _, },
        { rw is_open_compl_iff, rw set.range_prod_map, refine is_closed.prod _ _,
          { exact is_closed_discrete (set.range coe), },
          { apply is_closed_coe, }, }, }, },
    { rw ←open_embedding.open_iff_preimage_open _ at f1,
      { exact f1, },
      { intros z hz,
        rw set.mem_preimage at hz,
        by_cases h' : is_unit z.1 ∧ is_unit z.2,
        { rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
          rw prod.ext_iff, simp only [prod.map_mk], split, all_goals { rw is_unit.unit_spec, }, },
        { have : (ind_fn A p d f) z = 0, { rw ind_fn, simp only, convert dif_neg h', },
          exfalso, apply h, rw ←this, exact hz, }, },
      { constructor,
        { apply embedding.prod_mk,
          { constructor,
            { constructor, symmetry, convert top_eq_iff_cont_inv.2 _,
              convert continuous_of_discrete_topology, apply discrete_topology_induced,
              change function.injective coe, exact units.ext, },
            { exact units.ext, }, },
          { apply emb_coe, }, },
        { apply is_open_map.is_open_range,
          apply is_open_map.prod,
          { apply is_open_coe', },
          { apply is_open_coe, }, }, }, },
  end,
}

/-lemma subspace_induces_locally_constant [has_zero A] (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  ∃ (g : locally_constant (zmod d × ℤ_[p]) A),
    f.to_fun = g.to_fun ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
begin
  haveI : ∀ (x : zmod d), decidable (is_unit x),
  { intro x,
    exact classical.dec (is_unit x), },
  haveI : ∀ (x : ℤ_[p]), decidable (is_unit x),
  { intro x,
    exact classical.dec (is_unit x), },
  have f4 : is_open_map (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])),
  { apply is_open_map.prod,
    { apply is_open_coe', },
    { apply is_open_coe, }, },
  set g := λ x : (zmod d × ℤ_[p]),
    dite (is_unit x.1 ∧ is_unit x.2) (λ h, f (is_unit.unit h.1, is_unit.unit h.2)) (λ h, 0) with hg,
  have : f.to_fun = g ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])),
  { ext x, rw function.comp, simp only, rw hg, simp only,
    symmetry, convert dif_pos _,
    { rw prod.ext_iff, simp only [prod_map], split,
      all_goals { rw units.ext_iff,
        rw is_unit.unit_spec (units.is_unit _), }, },
    { simp only [units.is_unit, prod_map, and_self], }, },
  refine ⟨⟨g, _⟩, _⟩,
  { rw is_locally_constant,
    rintros s,
    have f1 := locally_constant.is_locally_constant f s,
    rw this at f1,
    rw set.preimage_comp at f1,
    by_cases (0 : A) ∈ s,
    { rw ←set.singleton_subset_iff at h,
      rw ←set.diff_union_of_subset h, rw set.preimage_union,
      apply is_open.union,
      { --copied same proof from below, how to reverse this? making new lemma required too many defs
        have f2 := locally_constant.is_locally_constant f (s \ {0}),
        rw this at f2,
        rw set.preimage_comp at f2,
        rw ←open_embedding.open_iff_preimage_open _ at f2,
        { exact f2, },
        { intros z hz,
          rw set.mem_preimage at hz,
          by_cases h' : is_unit z.1 ∧ is_unit z.2,
          { rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
            rw prod.ext_iff, simp only [prod.map_mk], split, all_goals { rw is_unit.unit_spec, }, },
          { have : g z = 0,
            { rw hg, convert dif_neg h', },
            exfalso, rw this at hz,
            simp only [set.mem_singleton, set.mem_diff, not_true, and_false] at hz, apply hz, }, },
        { constructor,
          { apply embedding.prod_mk,
            { constructor,
              { constructor, symmetry, convert top_eq_iff_cont_inv.2 _,
                convert continuous_of_discrete_topology, apply discrete_topology_induced,
                change function.injective coe, exact units.ext, },
              { exact units.ext, }, },
            { apply emb_coe, }, },
          { apply is_open_map.is_open_range,
            exact f4, }, }, },
      { have f3 : g⁻¹' {0} = (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p]))''
          (f⁻¹' {0}) ∪ (set.range (prod.map (coe : units (zmod d) → zmod d)
            (coe : units ℤ_[p] → ℤ_[p])))ᶜ,
        { ext y, rw set.mem_union, rw set.mem_preimage, rw set.mem_singleton_iff, split,
          all_goals { rintros h', },
          { rw hg at h',
            by_cases h'' : is_unit y.fst ∧ is_unit y.snd,
            { left, rw set.mem_image,
              refine ⟨(is_unit.unit h''.1, is_unit.unit h''.2), _, _⟩,
              { rw set.mem_preimage, rw set.mem_singleton_iff, rw ←h', symmetry, simp only,
                convert dif_pos h'', },
              { simp only [prod.map_mk], symmetry, rw prod.ext_iff, simp only, split,
                { rw is_unit.unit_spec h''.1, },
                { rw is_unit.unit_spec h''.2, }, }, },
            { right, contrapose h'', push_neg, rw ←set.mem_compl_iff at h'', rw compl_compl at h'',
              rw set.mem_range at h'', cases h'' with z hz, simp only [prod_map] at hz,
              rw prod.ext_iff at hz, simp only at hz, rw ←hz.1, rw ←hz.2,
              refine ⟨units.is_unit z.fst, units.is_unit z.snd⟩, }, },
          { rw hg, simp only, cases h',
            { rw set.mem_image at h', cases h' with z hz, convert dif_pos _,
              swap, { rw ←hz.2, simp only [units.is_unit, prod_map, and_self], },
              { symmetry, rw set.mem_preimage at hz, rw set.mem_singleton_iff at hz,
                rw prod.ext_iff at hz, cases hz with h1 h2, convert h1,
                symmetry, rw prod.ext_iff, rw units.ext_iff, simp only [prod_map] at h2,
                simp only, rw units.ext_iff, split,
                { convert h2.1, },
                { convert h2.2, }, }, },
            { convert dif_neg _, rw set.mem_compl_iff at h', contrapose h', push_neg at h',
              push_neg, rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
              symmetry, rw prod.ext_iff, simp only [prod.map_mk], rw is_unit.unit_spec (h').1,
              rw is_unit.unit_spec (h').2, refine ⟨rfl, rfl⟩, }, }, },
        rw f3, apply is_open.union,
        { apply f4 _, apply locally_constant.is_locally_constant f _, },
        { rw is_open_compl_iff, rw set.range_prod_map, refine is_closed.prod _ _,
          { exact is_closed_discrete (set.range coe), },
          { apply is_closed_coe, }, }, }, },
    { rw ←open_embedding.open_iff_preimage_open _ at f1,
      { exact f1, },
      { intros z hz,
        rw set.mem_preimage at hz,
        by_cases h' : is_unit z.1 ∧ is_unit z.2,
        { rw set.mem_range, refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), _⟩,
          rw prod.ext_iff, simp only [prod.map_mk], split, all_goals { rw is_unit.unit_spec, }, },
        { have : g z = 0, { rw hg, convert dif_neg h', },
          exfalso, apply h, rw ←this, exact hz, }, },
      { constructor,
        { apply embedding.prod_mk,
          { constructor,
            { constructor, symmetry, convert top_eq_iff_cont_inv.2 _,
              convert continuous_of_discrete_topology, apply discrete_topology_induced,
              change function.injective coe, exact units.ext, },
            { exact units.ext, }, },
          { apply emb_coe, }, },
        { apply is_open_map.is_open_range,
          apply is_open_map.prod,
          { apply is_open_coe', },
          { apply is_open_coe, }, }, }, }, },
  { convert this, },
end -/

--generalize to f : X → Y, Y compact, f cont and open, then X compact
instance : compact_space (units ℤ_[p]) :=
begin
  constructor,
  rw embedding.is_compact_iff_is_compact_image (emb_coe p),
  apply compact_of_is_closed_subset,
  swap 3, { apply set.subset_univ, },
  { exact compact_univ, },
  { convert is_closed_coe p, exact set.image_univ, },
end

lemma embedding_coe : embedding (coe : units ℤ_[p] → ℤ_[p]) :=
begin
  constructor,
  { rw (top_eq_iff_cont_inv.2 (cont_inv p)).symm,
    constructor,
    exact rfl, },
  { refine units.ext, },
end

instance is_this_even_true : compact_space (units (zmod d) × units ℤ_[p]) :=
  prod.compact_space

lemma disc_top_units : discrete_topology (units (zmod d)) :=
begin
  convert @discrete_topology_induced _ _ _ _ _ _,
  { apply @prod.discrete_topology _ _ _ _ (discrete_topology_bot (zmod d)) _,
    refine discrete_topology_induced (mul_opposite.unop_injective), },
  { intros x y h, rw units.embed_product at h,
    simp only [prod.mk.inj_iff, opposite.op_inj_iff, monoid_hom.coe_mk] at h,
    rw units.ext_iff, rw h.1, },
end

lemma t2_space_units : t2_space (units (zmod d)) := @t2_space_discrete _ _ (disc_top_units d)

lemma t2_space_units_padic : t2_space (units ℤ_[p]) :=
begin
  refine @embedding.t2_space _ _ _ _ _ ((units.coe_hom ℤ_[p]).to_fun) _,
  change embedding coe,
  apply embedding_coe,
end

--there are a LOT of lemmas in here, extract!
instance why_is_it_not_recognized : t2_space (units (zmod d) × units ℤ_[p]) :=
  @prod.t2_space _ _ _ (t2_space_units d) _ (t2_space_units_padic p)
--converting to the top ind by coe does not work well because zmod d is not a group :(

-- use injection of embed_product
instance so_many_times : totally_disconnected_space (units (zmod d) × units ℤ_[p]) :=
begin
  apply @prod.totally_disconnected_space _ _ _ _ _ _,
  { rw @compact_t2_tot_disc_iff_tot_sep _ _ (t2_space_units d) _,
    apply @totally_separated_space.of_discrete _ _ _,
    apply disc_top_units, },
  { constructor,
    apply embedding.is_totally_disconnected (embedding_coe p),
    exact is_totally_disconnected_of_totally_disconnected_space (coe '' set.univ), },
end

example {α : Type*} {s : set α} {x : α} (hx : x ∈ s) : s := ⟨x, hx⟩

@[to_additive] lemma locally_constant.prod_apply {B C : Type*} [topological_space B] [comm_monoid C] (n : ℕ)
  (f : ℕ → (locally_constant B C)) {x : B} :
  (∏ i in finset.range n, (f i)) x =
  ∏ i in finset.range n, ((f i) x) :=
begin
  induction n with d hd,
  { simp only [locally_constant.coe_one, finset.range_zero, finset.prod_empty, pi.one_apply], },
  { rw finset.prod_range_succ,
    rw locally_constant.mul_apply, rw hd,
    rw finset.prod_range_succ, },
end

lemma loc_const_eq_sum_char_fn (f : locally_constant ((zmod d) × ℤ_[p]) R) (hd : d.gcd p = 1) :
  ∃ n : ℕ, f = ∑ a in (finset.range (d * p^n)), f(a) • char_fn R (is_clopen_clopen_from p d n a) :=
begin
  set n := classical.some (factor_F _ _ _ hd f) with hn,
  refine ⟨n, _⟩,
  have := classical.some_spec (factor_F _ _ _ hd f),
  ext x,
  set x' := coe_padic_to_zmod p d n x hd with hx',
  rw locally_constant.sum_apply,
  /-convert_to _ = ∑ (a : ℕ) in finset.range (d * p ^ n), ((f a) • @char_fn _ _ _ _
    R _ _ _ (clopen_from p d n ↑a)) x,
  {
    rw locally_constant.add_apply,
    sorry, },-/
  { rw finset.sum_eq_single_of_mem,
    swap 4, { exact x'.val, },
    swap 2, { rw finset.mem_range, apply zmod.val_lt _, apply fact_iff.2, apply mul_prime_pow_pos, },
    { simp,
      --simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, locally_constant.coe_smul,
        --pi.smul_apply, zmod.nat_cast_val],
      rw ←mul_one (f x),
      convert @locally_constant.smul_apply (zmod d × ℤ_[p]) R infer_instance R infer_instance
        (f x') (char_fn R (is_clopen_clopen_from p d n x')) x using 1,
      rw locally_constant.smul_apply, rw smul_eq_mul,
      apply congr_arg2,
      { apply this, rw F_rel, simp only [prod.fst_zmod_cast],
        refine ⟨_, proj_fst p d n _ _⟩, rw hx', rw coe_padic_to_zmod,
        conv_rhs { rw ←proj_snd, skip,
          apply_congr coprime_pow_spl p d n hd, },
        simp,
        have : ∀ x : zmod (d * p^n), to_zmod_pow n (x : ℤ_[p]) = (x : zmod (p^n)),
        { rintros x, rw ←zmod.int_cast_cast x,
          change (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom ℤ_[p])) (x : ℤ) = coe x,
          rw ring_hom.eq_int_cast _ (x : ℤ),
          rw zmod.int_cast_cast, },
        rw this, },
      { symmetry,
        rw ←char_fn_one, rw mem_clopen_from', exact (F p d n).refl x, }, },
    { rintros b hb h, rw ←smul_zero (f b),
      rw locally_constant.smul_apply, congr,
      rw char_fn, simp only [ite_eq_right_iff, one_ne_zero, locally_constant.coe_mk],
      intro h', apply h,
      --rw this at h',
      --rw mem_clopen_from at h',
      suffices : (b : zmod (d * p^n)) = x',
      { rw ←zmod.nat_cast_zmod_val x' at this,
        convert congr_arg (zmod.val) this,
        { rw zmod.val_cast_of_lt _,
          rw ←finset.mem_range, assumption, },
        { rw zmod.nat_cast_zmod_val _,
          apply fact_iff.2, apply mul_prime_pow_pos, }, },
      { --rw h2 at h',
        rw mem_clopen_from at h', rw eq_comm at h', --have h'' := this _ _ h',
        --have h3 := discrete_quotient.eq_of_proj_eq (locally_constant.discrete_quotient f),
        rw ←equiv.apply_eq_iff_eq (zmod.chinese_remainder (coprime_pow_spl p d n hd)).to_equiv,
        rw prod.ext_iff, repeat { rw inv_fst', rw inv_snd', },
        rw hx', rw coe_padic_to_zmod, rw proj_fst, rw proj_snd, assumption, }, }, },
end

noncomputable instance {α : Type*} [topological_space α] [monoid α] (x : α) : decidable (is_unit x) :=
 classical.dec (is_unit x)

/- -- For semi_normed_space
example [semi_normed_space ℚ R] {x : ℚ} : ∥(algebra_map ℚ R) x∥ ≤ ∥x∥ :=
begin
  rw algebra.algebra_map_eq_smul_one, have := norm_smul x (1 : R),

  have := (semi_normed_space.norm_smul_le x (1 : R)), -- has mul_action.to_has_scalar
  convert le_trans this _ using 1,
  { apply congr_arg,
    sorry, },
  { have : ∥x∥ * ∥(1 : R)∥ ≤ ∥x∥ * ∥(1 : ℚ)∥,
    { apply mul_le_mul (le_refl _),
      { rw ←one_smul ℚ (1 : R),
        have := (semi_normed_space.norm_smul_le (1 : ℚ) (1 : R)),
        apply le_trans this _,
        sorry, },
      sorry,
      sorry, },
    apply le_trans this _,
    rw norm_one, rw mul_one,
    sorry, },
end -/

--generalize
lemma nat.one_lt_mul_of_ne_one (k : ℕ) (h : d * p^k ≠ 1) : 1 < d * p^k :=
begin
  change 1 < _,
  rw nat.one_lt_iff_ne_zero_and_ne_one,
  refine ⟨nat.mul_ne_zero _ _, h⟩,
  --why does apply_instance not work? is there an easier way?
  { apply ne_zero_of_lt (fact.out _), exact 0, swap 2, convert _inst_9, },
  { apply pow_ne_zero _ (nat.prime.ne_zero (fact.out _)), apply_instance, },
end

lemma nat.coprime_mul_pow (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (n : ℕ) : c.coprime (d * p^n) :=
nat.coprime.mul_right hc' (nat.coprime_pow_spl p c n hc)

lemma exists_V_h1_1 (hc' : c.coprime d) (hc : c.coprime p) (k : ℕ) :
  ∃ z : ℕ, c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k))
  (λ h, 1 + z * (d * p^(2 * k))) (λ h, 0) :=
begin
  have c_cop : c.coprime (d * p^(2 * k)) := nat.coprime_mul_pow p d hc hc' (2 * k),
  by_cases eq_one : (d * p^(2 * k)) = 1,
  { have k_zero : ¬ 1 < d * p^(2 * k),
    { rw eq_one, simp only [nat.lt_one_iff, nat.one_ne_zero, not_false_iff], },
    refine ⟨1, _⟩, rw dif_neg k_zero,
    rw eq_one, simp only [nat.mul_eq_zero, zmod.val_eq_zero, eq_iff_true_of_subsingleton, or_true], },
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1, simp,
    rw ← this,
    rw zmod.val_cast_of_lt (nat.one_lt_mul_of_ne_one p d _ eq_one), },
  simp_rw dif_pos (nat.one_lt_mul_of_ne_one p d _ eq_one),
  conv { congr, funext, find 1 {rw ← h}, },
  conv { congr, funext, rw mul_comm z _, },
  apply (zmod.nat_coe_zmod_eq_iff _ _ _).1 _,
  { apply imp p d _, },
  { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ c_cop _,
    rw zmod.cast_nat_cast _, apply zmod.coe_mul_inv_eq_one _ c_cop,
    swap 2, { refine zmod.char_p _, },
    any_goals { apply dvd_rfl, }, },
end
.

--generalize
lemma nat.mul_pow_eq_one_of_mul_pow_sq_not_one_lt {n : ℕ} (h : ¬ 1 < d * p^(2 * n)) : d * p^n = 1 :=
begin
  rw not_lt_iff_eq_or_lt at h,
  simp only [lt_one_iff, nat.mul_eq_zero] at h,
  cases h,
  { have h' := h.symm,
    rw nat.mul_eq_one_iff at h', rw pow_mul' at h', rw pow_succ at h', rw pow_one at h',
    rw nat.mul_eq_one_iff at h',
    rw h'.1, rw h'.2.1, rw one_mul, },
  { have p1 : d ≠ 0,
    { apply ne_zero_of_lt (fact.out _),
      exact 0,
      apply_instance,
      apply_instance, },
    have p2 : p^(2 * n) ≠ 0,
    { apply pow_ne_zero, apply nat.prime.ne_zero (fact.out _), apply_instance, },
    simp only [p1, p2, or_self] at h,
    exfalso, exact h, },
end

lemma helper_meas_E_c {n : ℕ} (a : zmod (d * p^n)) (hc' : c.coprime d) (hc : c.coprime p) : ∃ z : ℤ,
  int.fract ((a.val : ℚ) / (↑d * ↑p ^ n)) -
  ↑c * int.fract (↑((c : zmod (d * p^(2 * n)))⁻¹.val) * (a : ℚ) / (↑d * ↑p ^ n)) = z :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat ((↑((c : zmod (d * p^(2 * n)))⁻¹.val) * (a : ℚ) / (↑d * ↑p ^ n))) c,
  obtain ⟨z', hz'⟩ := exists_V_h1_1 p d hc' hc n,
  rw mul_comm at hz, rw mul_comm _ (c : ℚ) at hz, rw ← mul_div at hz, rw ← mul_assoc at hz,
  rw ← nat.cast_mul at hz,
  by_cases pos : 1 < d * p^(2 * n),
  { rw dif_pos pos at hz',
    rw hz' at hz, rw nat.cast_add at hz, rw nat.cast_one at hz, rw one_add_mul at hz,
    conv at hz { congr, congr, skip, congr, congr, skip, congr, rw pow_mul', rw pow_succ, rw pow_one, },
    rw ← mul_assoc d (p^n) at hz,
    rw mul_comm (d * p^n) (p^n) at hz, rw ← mul_assoc z' _ _ at hz, rw nat.cast_mul at hz,
    rw mul_comm _ (↑(d * p ^ n)) at hz, rw mul_assoc at hz, rw mul_div (↑(z' * p ^ n)) _ _ at hz,
    rw ← nat.cast_pow at hz, rw ← nat.cast_mul at hz, rw mul_div_cancel' at hz,
    rw ← zmod.nat_cast_val at hz, rw ← nat.cast_mul at hz,
    rw ← int.cast_coe_nat (z' * p ^ n * a.val) at hz,
    rw int.fract_add_int at hz,
    refine ⟨-z, _⟩,
    rw int.cast_neg, rw ← hz, rw neg_sub, rw zmod.nat_cast_val a,
    rw nat.cast_mul d _, rw nat.cast_pow, rw mul_div,
    { norm_cast, apply ne_zero_of_lt (fact_iff.1 (imp p d n)), }, },
  { have pos' : d * (p^n) = 1,
    { apply nat.mul_pow_eq_one_of_mul_pow_sq_not_one_lt p d pos, },
    simp_rw [← nat.cast_pow, ← zmod.nat_cast_val a, ← nat.cast_mul, pos', nat.cast_one, div_one,
      ← int.cast_coe_nat],
    refine ⟨0, _⟩,
    rw int.cast_zero, simp_rw int.fract_coe, rw mul_zero, rw sub_zero, },
end

lemma meas_E_c [normed_algebra ℚ_[p] R] (n : ℕ) {a : zmod (d * p^n)} (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (h' : d.gcd p = 1) : ∥ (classical.some (@set.nonempty_of_nonempty_subtype _ _
  (bernoulli_measure_nonempty p d R hc hc' h'))) (char_fn R (is_clopen_clopen_from p d n a))∥ ≤
  1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ :=
begin
  have := (classical.some_spec (@set.nonempty_of_nonempty_subtype _ _
  (bernoulli_measure_nonempty p d R hc hc' h'))),
  rw set.mem_def at this,
  specialize this n a,
  --rw clopen_from,
  rw this,

  rw is_scalar_tower.algebra_map_apply ℚ ℚ_[p] R, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,

  /-convert_to ∥(E_c p d hc n a)∥ ≤ _,
  {
    rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one, }, -/
  rw E_c, simp only,
  obtain ⟨z, hz⟩ := helper_meas_E_c p d a hc' hc,
  rw ring_hom.map_add,

  apply le_trans (norm_add_le _ _) _,
  apply add_le_add_right _ _,
  { apply_instance, },
  { rw hz, rw ring_hom.map_int_cast,
    apply padic_norm_e.norm_int_le_one z, },

    /-apply le_trans (norm_sub_le _ _) _,
    have : ∀ (x : ℚ), ∥int.fract x∥ ≤ 1, --should be separate lemma
    { intro x, convert_to ∥((int.fract x : ℚ) : ℝ)∥ ≤ 1, rw real.norm_of_nonneg _,
      { norm_cast, apply le_of_lt, apply int.fract_lt_one, },
      { norm_cast, apply int.fract_nonneg, }, },
    apply add_le_add,
    { sorry, --apply this,
     },
    { rw ←mul_one (∥(c : ℚ_[p])∥),
      rw ring_hom.map_mul,

      apply le_trans (norm_mul_le _ _) _,
      rw map_nat_cast,
      apply mul_le_mul_of_nonneg_left _ _,
      { sorry, --apply this _,
       },
      { apply norm_nonneg, }, }, }, -/
end

lemma smul_eq_mul' {α β : Type*} [topological_space α] [ring β] (f : locally_constant α β)
  (b : β) : b • f = (locally_constant.const α b) * f :=
begin
  ext,
  simp only [locally_constant.coe_const, locally_constant.coe_mul, pi.mul_apply,
  locally_constant.coe_smul, smul_eq_mul, pi.smul_apply],
end

--noncomputable instance : semi_normed_ring (C((zmod d × ℤ_[p]), R)) := infer_instance

noncomputable instance : normed_ring (locally_constant (zmod d × ℤ_[p]) R) :=
begin
  constructor,
  { rintros x y, exact dist_eq_norm x y, },
  { rintros a b,
    convert_to ∥inclusion _ _ a * inclusion _ _ b∥ ≤ ∥inclusion _ _ a∥ * ∥inclusion _ _ b∥,
    convert @norm_mul_le (C(zmod d × ℤ_[p], R)) (infer_instance) _ _, },
end

example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := mul_nonneg ha hb

lemma s_nonempty (n : ℕ) (f : locally_constant (units (zmod d) × units ℤ_[p]) R) (a : ℝ)
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (ha : a = ⨆ (i : zmod (d * p ^ n)),
      ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
      (bernoulli_measure_nonempty p d R hc hc' h')))
      (((loc_const_ind_fn R p d f) ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n (i.val)))∥) :
  {i : zmod (d * p^n) | ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
      (bernoulli_measure_nonempty p d R hc hc' h')))
    ((loc_const_ind_fn R p d f) ↑(i.val) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a }.nonempty :=
begin
  have := set.nonempty.cSup_mem,
  swap 4, { refine set.range (λ (i : zmod (d * p^n)),
    ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _ (bernoulli_measure_nonempty p d R hc hc' h')))
    ((loc_const_ind_fn R p d f) ↑i • char_fn R (is_clopen_clopen_from p d n i))∥), },
  swap, { apply_instance, },
  specialize this _ _,
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { rw ←set.image_univ, apply set.finite.image, exact set.finite_univ, },
  { suffices : a ∈ set.range (λ (i : zmod (d * p^n)),
      ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _ (bernoulli_measure_nonempty p d R hc hc' h')))
      ((loc_const_ind_fn R p d f) ↑i • char_fn R (is_clopen_clopen_from p d n i))∥),
    { cases this with y hy,
      simp only [algebra.id.smul_eq_mul, linear_map.map_smul] at hy,
      use y,
      simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, set.mem_set_of_eq,
        finset.mem_range, linear_map.map_smul, zmod.nat_cast_val],
      refine hy, },
    { convert this using 1, rw ha,
      convert_to Sup (set.range (λ (i :zmod (d * p ^ n)),
        ∥(classical.some (@set.nonempty_of_nonempty_subtype _ _
        (bernoulli_measure_nonempty p d R hc hc' h')))
      (((loc_const_ind_fn R p d f) ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥)) = _,
      refine congr_arg _ _,
      simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end
