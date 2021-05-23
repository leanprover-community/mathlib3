import tactic
import representation_theory.main
import representation_theory.main2
import representation_theory.pi_map
import representation_theory.pi_map2
import linear_algebra.direct_sum_module

open_locale direct_sum classical big_operators direct_sum
open classical linear_map finite_dimensional
noncomputable theory
/-!
# Simple Modules

-/

universes u v w

variables (R : Type u) [ring R] (M : Type v) [add_comm_group M] [module R M] [is_semisimple_module R M]

lemma is_internal_of_semisimple [nontrivial R] :
  ∃ (S : set (submodule R M)), complete_lattice.set_independent S ∧ (∀ s ∈ S, is_atom s) ∧ Sup S = ⊤ ∧
    direct_sum.submodule_is_internal (λ m : S, m.val) :=
begin
  letI : is_atomistic (submodule R M) := by apply_instance,
  obtain ⟨s, s_ind, s_top, s_atom⟩ := is_atomistic.exist_set_independent_Sup_eq_top,
  refine ⟨s, s_ind, s_atom, s_top, _⟩,
  rw Sup_eq_supr' at s_top,
  let e : (⨁ m : s, m) ≃ₗ[R] (⊤ : submodule R M),
  { let e1 := submodule.prod_equiv_of_independent (λ m : s, m.val) ((complete_lattice.set_independent_iff s).mp s_ind),
    exact e1.trans (dumb_map s_top), },
  have : ∀ x, (↑(e x) : M) = ↑((terrible_map (λ m : s, m.val)) x),
  { intro x,
    simp [e, dumb_map, submodule.prod_equiv_of_independent] },
  let E := e.trans (submodule.top_equiv R M),
  rw direct_sum.submodule_is_internal,
  convert linear_equiv.bijective E,
  { ext, simp only [submodule.top_equiv, dfinsupp.lsingle_apply, function.comp_app,
      linear_equiv.coe_mk, linear_equiv.coe_to_linear_map, coe_comp, subtype.val_eq_coe],
    rw this (dfinsupp.single i x),
    simp only [terrible_map_apply],
    rw to_module_apply' s _,
    simp only [dfinsupp.single_apply, subtype.val_eq_coe],
    rw coe_sum,
    simp only [submodule.coe_mk],
    refl, },
  all_goals { apply_instance },
end

theorem supr_eq_Sup {ι : Type v}
  {α : Type u} [complete_lattice α] [is_compactly_generated α] {a : α} {f : ι → α} :
  supr f = Sup (set.univ) :=
begin
  simp,
end

theorem inf_supr_eq_supr_inf_sup_finset {ι : Type v}
  {α : Type u} [complete_lattice α] [is_compactly_generated α] {a : α} {f : ι → α} :
  a ⊓ supr f = ⨆ (t : finset ι), a ⊓ t.sup f :=
begin
  rw ← Sup_eq_supr,
end

theorem disjoint.disjoint_finset_sup {α : Type u} [bounded_lattice α] [is_modular_lattice α]
  {ι : Type v} {b : ι → α} (s : finset ι) (a : α)
  (h : ∀ i ∈ s, disjoint a (b i)) (hsup : ∀ i j, disjoint (a ⊔ i) j) :
  disjoint a (s.sup b) :=
begin
  apply finset.sup_induction,
  exact disjoint_bot_right,
  intros i j hi hj,
  exact disjoint.disjoint_sup_right_of_disjoint_sup_left hi (hsup i j),
  intros i hi,
  exact h i hi,
end

theorem disjoint.disjoint_Sup_right_of_disjoint_Sup_left
  {α : Type u} [complete_lattice α] [is_modular_lattice α] {ι : Type v}
  {a : α} {b : ι → α} (h : ∀ i, disjoint a (b i)) (hsup : ∀ i j, i ≠ j → disjoint (a ⊔ b i) (b j)) (i : ι) :
  disjoint a (⨆ i, b i) :=
begin
  rw disjoint, rw \l Sup_eq_supr,
  rw inf_Sup_eq_supr_inf_sup_finset,
end

/-- should be is_semisimple_module.decomposition -/
def decomposition [nontrivial R] : set (submodule R M) :=
  (is_internal_of_semisimple R M).some

/-- should be is_semisimple_module.set_independent_decomposition -/
lemma set_independent_decomposition [nontrivial R] :
  complete_lattice.set_independent (decomposition R M) :=
(is_internal_of_semisimple R M).some_spec.1

lemma independent_decomposition [nontrivial R] :
  complete_lattice.independent (λ m : decomposition R M, m.val) :=
(complete_lattice.set_independent_iff (decomposition R M)).mp (set_independent_decomposition _ _)

lemma Sup_decomposition_eq_top [nontrivial R] :
  Sup (decomposition R M) = ⊤ :=
(is_internal_of_semisimple R M).some_spec.2.2.1

lemma supr_decomposition_eq_top [nontrivial R] :
  supr (λ m : decomposition R M, m.val) = ⊤ :=
begin
  rw ← Sup_decomposition_eq_top,
  exact Sup_eq_supr'.symm,
end

def decomposition_equiv [nontrivial R] :
  (⨁ m : decomposition R M, m) ≃ₗ[R] M :=
is_decomposition.equiv R M (λ m : decomposition R M, m.val)
  (independent_decomposition R M) (supr_decomposition_eq_top R M)

lemma mem_decomposition_is_atom [nontrivial R] (m : submodule R M) :
  m ∈ (decomposition R M) → is_atom m :=
(is_internal_of_semisimple R M).some_spec.2.1 m

instance submodule.isomorphism_classes : setoid (submodule R M) :=
{ r := λ n m, nonempty (n ≃ₗ[R] m),
  iseqv := ⟨λ x, ⟨linear_equiv.refl R x⟩, λ x y h, ⟨h.some.symm⟩,
    λ x y z hxy hyz, ⟨hxy.some.trans hyz.some⟩⟩ }

def decomposition.classes [nontrivial R] : setoid (decomposition R M) := subtype.setoid (∈ (decomposition R M))

def setoid.class {α : Type*} (r : setoid α) (y : α) := {x : α | r.rel x y}

variables {R M}

def decomposition.class [nontrivial R] (m : submodule R M) (hm : m ∈ (decomposition R M)) :=
  setoid.class (decomposition.classes R M) ⟨m, hm⟩

def decomposition.class' [nontrivial R] (m : submodule R M) :=
  setoid.class (submodule.isomorphism_classes R M) m

variables [nontrivial R]
variables (m : submodule R M) (hm : m ∈ (decomposition R M))
#check supr (λ n : decomposition.class m hm, n.val.val)

variables (R M)

def isomorphism_quot [nontrivial R] := quotient (decomposition.classes R M)

variables {R M}

def quotient.class [nontrivial R] (i : isomorphism_quot R M) := decomposition.class i.out.1 i.out.2

variables (R M)

def iso_rel [nontrivial R] {i : isomorphism_quot R M}
  (m : quotient.class i) : m ≃ₗ[R] i.out := m.2.some

attribute [irreducible] quotient.class decomposition


def supr_class [nontrivial R] :=
λ m : isomorphism_quot R M, supr (λ n : quotient.class m, n.1.1)

variables {R M}

lemma partition_independent [nontrivial R] : complete_lattice.independent (supr_class R M) :=
begin
  sorry
end

lemma is_atom_ne_bot {α : Type u} [order_bot α] {a b : α} (ha : is_atom a) : a ≠ ⊥ :=
begin
  rw is_atom at ha,
  exact ha.1,
end

lemma submodule.nonempty_of_is_atom (m : submodule R M) (h : is_atom m) :
  ∃ x ∈ m, x ≠ (0 : M) :=
begin
  by_contradiction hx,
  push_neg at hx,
  have : m = ⊥, rwa submodule.eq_bot_iff,
  apply is_atom_ne_bot h,
  exact this,
  exact m,
end

instance does_this_work [nontrivial R] [is_semisimple_module R R] : fintype (decomposition R R) :=
{ elems := ((decomposition_equiv R R).symm 1).support,
  complete := λ m,
  begin
    rw dfinsupp.mem_support_iff,
    have := mem_decomposition_is_atom R R m.1 m.2,
    rcases submodule.nonempty_of_is_atom m.1 this with ⟨x, hm, hx⟩,
    have h1 : ((decomposition_equiv R R).symm x) = (x • (decomposition_equiv R R).symm 1),
    { have : x • 1 = x, rw [smul_eq_mul, mul_one],
      conv_lhs { rw ← this },
      rw linear_equiv.map_smul (decomposition_equiv R R).symm x (1 : R), },
    have h2 : ((decomposition_equiv R R).symm x) m ≠ 0,
    { have := is_decomposition.equiv_symm_single_apply R R (λ m : decomposition R R, m.val)
        (independent_decomposition R R) (supr_decomposition_eq_top R R) m x hm,
      simp only [decomposition_equiv, this, dfinsupp.single_eq_same],
      simp only [ne.def, submodule.mk_eq_zero, hx],
      exact not_false, },
    rw h1 at h2,
    simp only [dfinsupp.coe_smul, pi.smul_apply] at h2,
    revert h2,
    contrapose!,
    intros h,
    rw h,
    rw smul_zero,
  end }

lemma quotient.out_mk' {α : Type u} {s : setoid α} (a : α) : s.rel (quotient.mk' a).out a :=
quotient.exact (quotient.out_eq _)

lemma supr_classes_eq_top [nontrivial R] [is_semisimple_module R R] :
  (⨆ (i : isomorphism_quot R R), supr_class R R i) = ⊤ :=
begin
  rw supr_class,
  dsimp,
  rw eq_top_iff,
  rw ← Sup_decomposition_eq_top,
  refine Sup_le (λ b hb, _),
  refine le_supr_of_le _ _,
  exact quotient.mk' ⟨b, hb⟩,
  refine le_Sup _,
  rw quotient.class,
  rw decomposition.class,
  rw setoid.class,
  simp only [quotient.mk_out, exists_prop, set.mem_range, set_coe.exists, exists_and_distrib_right, exists_eq_right,
  subtype.coe_eta, set.mem_set_of_eq, subtype.coe_mk],
  use hb,
  symmetry,
  exact quotient.mk_out (⟨b, hb⟩ : decomposition R R),
end

lemma quotient_class_ind [nontrivial R] [is_semisimple_module R M] (i : isomorphism_quot R M) :
  complete_lattice.independent (λ m : quotient.class i, m.val.val) :=
begin
  change complete_lattice.independent coe,
  rw complete_lattice.independent_def,
  rw quotient.class,
  rw decomposition.class,
  rw setoid.class,
  simp only [ne.def, set_coe.forall, subtype.coe_eta, set.mem_set_of_eq, subtype.coe_mk,
    subtype.val_eq_coe, coe_coe],
  intros x hx hx',
  simp only [ne.def, subtype.coe_mk],
  have := independent_decomposition R M,
  rw complete_lattice.independent_def at this,
  rw set_coe.forall at this,
  refine disjoint.mono_right _ (this x hx),
  refine supr_le _,
  rw set_coe.forall,
  rw set_coe.forall,
  intros y hy hy',
  simp only [supr_le_iff, subtype.mk_eq_mk, ne.def, subtype.coe_mk, subtype.val_eq_coe],
  intro h,
  rw supr,
  refine le_Sup _,
  rw set.mem_range,
  use y,
  exact hy,
  simp [h],
end

def step1 [nontrivial R] [is_semisimple_module R R] :
  (⨁ (i : isomorphism_quot R R), supr_class R R i) ≃ₗ[R] R :=
  is_decomposition.equiv R R (supr_class R R) partition_independent (supr_classes_eq_top)

def step2 [nontrivial R] [is_semisimple_module R R] (i : isomorphism_quot R R) :
  supr_class R R i ≃ₗ[R] ⨁ m : (quotient.class i), m :=
(submodule.prod_equiv_of_independent (λ m : quotient.class i, m.1.1) (quotient_class_ind i)).symm

def direct_sum.linear_equiv {ι : Type v} [dec_ι : decidable_eq ι] {R : Type u} [semiring R]
  {α : ι → Type w} [Π (i : ι), add_comm_monoid (α i)] [Π (i : ι), module R (α i)]
  {β : ι → Type w} [Π (i : ι), add_comm_monoid (β i)] [Π (i : ι), module R (β i)]
  (h : ∀ i, α i ≃ₗ[R] β i) : (⨁ i, α i) ≃ₗ[R] ⨁ i, β i :=
dfinsupp.map_range.linear_equiv h

def step3 [nontrivial R] [is_semisimple_module R R] (i : isomorphism_quot R R) :
  (⨁ m : (quotient.class i), m) ≃ₗ[R] (quotient.class i) →₀ i.out :=
{ to_fun := λ x,
  { support := x.support,
    to_fun := λ m, iso_rel R R m (x m),
    mem_support_to_fun := λ m,
    begin
      sorry
    end },
  map_add' := λ x y,
  begin
    ext,
    simp only [pi.add_apply, linear_equiv.map_add, direct_sum.add_apply,
      finsupp.coe_add, finsupp.coe_mk],
  end,
  map_smul' := λ x y,
  begin
    ext,
    simp only [dfinsupp.coe_smul, linear_equiv.map_smul, finsupp.coe_smul,
      pi.smul_apply, finsupp.coe_mk],
  end,
  inv_fun := λ x, direct_sum.mk _ x.support (λ m, (iso_rel R R m.1).symm (x m.1)),
  left_inv := λ x, by { ext m, dsimp only,
    simp only [finsupp.coe_mk],
    simp only [set_like.coe_eq_coe, linear_equiv.symm_apply_apply, direct_sum.mk, add_monoid_hom.coe_mk],
    rw @dfinsupp.mk_apply _ _ _ _ x.support (λ (m : ↥↑(x.support)), x m.1) m,
    split_ifs,
    congr,
    revert h,
    contrapose!,
    intro h,
    rw dfinsupp.mem_support_iff _ m,
    exact h.symm, },
  right_inv := λ x,
  begin
    ext m, dsimp only,
    simp only [finsupp.coe_mk, set_like.coe_eq_coe, direct_sum.mk, add_monoid_hom.coe_mk],
    have := @dfinsupp.mk_apply _ _ _ _ x.support (λ (m : ↥↑(x.support)), (iso_rel R R m.val).symm (x m.val)) m,
    simp only [this],
    split_ifs,
    convert linear_equiv.apply_symm_apply (iso_rel R R m) (x m),
    rw linear_equiv.map_zero,
    revert h, contrapose!,
    intro h,
    rw finsupp.mem_support_iff,
    exact h.symm,
  end }


instance bruh [nontrivial R] [is_semisimple_module R R] :
  Π (i : isomorphism_quot R R), add_comm_monoid ((quotient.class i →₀ i.out)) :=
λ i, by apply_instance


instance bruh2 [nontrivial R] [is_semisimple_module R R] :
  Π (i : isomorphism_quot R R), module R ((quotient.class i →₀ i.out)) :=
λ i, by apply_instance

def step4 [nontrivial R] [is_semisimple_module R R] :
  (⨁ (i : isomorphism_quot R R), (quotient.class i) → i.out) ≃ₗ[R] R :=
(direct_sum.linear_equiv (λ i, ((step2 i).trans (step3 i)).trans
  (finsupp.linear_equiv_fun_on_fintype R))).symm.trans step1

instance bruh3 [nontrivial R] [is_semisimple_module R R] : fintype (isomorphism_quot R R) :=
  quotient.fintype (decomposition.classes R R)

instance bruh4 [nontrivial R] [is_semisimple_module R R] :
  Π i : isomorphism_quot R R, fintype (quotient.class i) :=
λ i, by apply_instance

def dfinsupp.equiv_fun_on_fintype {ι : Type*} {M : ι → Type*}
  [∀ i, has_zero (M i)] [fintype ι] :
  (Π₀ i, M i) ≃ (Π i, M i) :=
{ to_fun := λ f a, f a,
  inv_fun := λ f, dfinsupp.mk finset.univ (λ x, f x),
  left_inv := λ f, by { ext, simp, congr, },
  right_inv := λ f, by { ext, simp, congr, }, }

def dfinsupp.linear_equiv_fun_on_fintype {ι : Type*} {R : Type*} {M : ι → Type*}
  [semiring R] [∀ i, add_comm_monoid (M i)] [∀ i, module R (M i)] [fintype ι] :
  (Π₀ i, M i) ≃ₗ[R] (Π i, M i) :=
{ map_add' := λ x y, by { ext, simp [dfinsupp.equiv_fun_on_fintype], },
  map_smul' := λ x y, by { ext, simp [dfinsupp.equiv_fun_on_fintype], },
  ..dfinsupp.equiv_fun_on_fintype }

def module.End_equiv {R : Type u} {M N : Type v} [semiring R] [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N] (e : M ≃ₗ[R] N) : module.End R M ≃+* module.End R N :=
{ to_fun := λ f,
  { to_fun := λ x, e (f (e.symm x)),
    map_add' := λ x y, by { simp only [linear_equiv.map_add, linear_map.map_add], },
    map_smul' := λ x y, by { simp only [linear_equiv.map_smul, linear_map.map_smul], } },
  inv_fun := λ f,
  { to_fun := λ x, e.symm (f (e x)),
    map_add' := λ x y, by { simp only [linear_equiv.map_add, linear_map.map_add], },
    map_smul' := λ x y, by { simp only [linear_equiv.map_smul, linear_map.map_smul], } },
  left_inv := λ x, by { ext, simp only [coe_mk, linear_equiv.symm_apply_apply], },
  right_inv := λ x, by { ext, simp only [coe_mk, linear_equiv.apply_symm_apply], },
  map_mul' := λ x y, by { ext, simp only [coe_mk, mul_apply, linear_equiv.symm_apply_apply], },
  map_add' := λ x y, by { ext, simp only [coe_mk, add_apply, linear_equiv.map_add], }, }


def step5 [nontrivial R] [is_semisimple_module R R] :
  (Π (i : isomorphism_quot R R), (quotient.class i) → i.out) ≃ₗ[R] R :=
dfinsupp.linear_equiv_fun_on_fintype.symm.trans step4

def helpful_coe [nontrivial R] [is_semisimple_module R M] (i : isomorphism_quot R M) :
  i.out →ₗ[R] M :=
{ to_fun := λ x, x,
  map_add' := λ x y, rfl,
  map_smul' := λ m x, rfl }

lemma helpful_thing [nontrivial R] [is_semisimple_module R R] (i : isomorphism_quot R R)
  (m n : submodule R i.out) : m = n ↔ m.map (helpful_coe i) = n.map (helpful_coe i) :=
begin
  split,
  intro h,
  rw h,
  intro h,
  have h1 : function.injective (helpful_coe i),
  { intros a b hab, simp only [helpful_coe, coe_mk, set_like.coe_eq_coe] at hab, exact hab, },
  have h2 : function.injective (submodule.map (helpful_coe i)),
  { sorry },
  apply_fun submodule.map (helpful_coe i), exact h,
end

lemma helpful_thing2 [nontrivial R] [is_semisimple_module R R] (i : isomorphism_quot R R) :
  submodule.map (helpful_coe i) ⊤ = i.out :=
begin
  ext,
  simp only [submodule.map_top, helpful_coe, coe_mk, mem_range],
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with y hy,
    rw ← hy,
    exact y.2, },
  use ⟨x, h⟩,
  exact subtype.coe_mk _ _,
end

instance out_is_simple [nontrivial R] [is_semisimple_module R R] :
  Π (i : isomorphism_quot R R), is_simple_module R i.out :=
λ i,
{ exists_pair_ne :=
  by { use ⊥, use ⊤,
    have := not_iff_not.mpr (helpful_thing i ⊥ ⊤), rw ne.def, rw this, rw ← ne.def,
    rw helpful_thing2,
    rw submodule.map_bot,
    have := mem_decomposition_is_atom R R i.out.1 i.out.2,
    rw ← subtype.val_eq_coe,
    have hhh := (is_atom_ne_bot this).symm,
    exact hhh,
    exact i.out.1, },
  eq_bot_or_eq_top := λ m,
  begin
    have h1 := (mem_decomposition_is_atom R R i.out.1 i.out.2),
    have h2 : m.map (helpful_coe i) ≤ i.out.1,
    { rw subtype.val_eq_coe,
      rw ← helpful_thing2,
      exact submodule.map_mono le_top },
    have h3 := eq_bot_or_eq_of_le_atom h1 h2,
    cases h3,
    { left,
      rw helpful_thing,
      rw submodule.map_bot,
      exact h3, },
    right,
    rw helpful_thing,
    rw helpful_thing2,
    exact h3,
  end }

lemma step6_aux [nontrivial R] [is_semisimple_module R R] :
  pairwise (λ (i j : isomorphism_quot R R),
  ∀ (f : ((quotient.class i) → i.out) →ₗ[R] (quotient.class j) → j.out), f = 0) :=
begin
  intros i j hij f,
  ext m x n,
  suffices h : f (pi.single m x) n = 0,
  { simp only [coe_single, pi.zero_apply, function.comp_app, submodule.coe_zero,
      submodule.coe_eq_zero, coe_comp, zero_apply],
    exact h },
  let g := (linear_map.proj n).comp (f.comp (linear_map.single m)),
  have hg : g = 0,
  { apply or.resolve_left (bijective_or_eq_zero g),
    revert hij, contrapose!, intro hg,
    have : quotient.mk i.out = quotient.mk j.out := quotient.sound ⟨linear_equiv.of_bijective g _ _⟩,
    rw quotient.out_eq at this,
    rwa quotient.out_eq at this,
    exact ker_eq_bot_of_injective hg.injective,
    exact range_eq_top.mpr hg.surjective },
  have key : ∀ x, g x = f (pi.single m x) n, { intro x, refl, },
  rw ← key x,
  simp only [hg, zero_apply],
end

def step6 [nontrivial R] [is_semisimple_module R R] :
  (Π (i : isomorphism_quot R R), module.End R (quotient.class i → i.out)) ≃+* module.End R R :=
(linear_map.End_pi_linear_equiv R (λ i, quotient.class i → i.out) (by { exact step6_aux })).symm.trans
  (module.End_equiv step5)

def ring_equiv.pi {ι : Type u} {R : ι → Type v} {S : ι → Type w}
  [Π i, semiring (R i)] [Π i, semiring (S i)] (e : Π i, R i ≃+* S i) :
  (Π i, R i) ≃+* (Π i, S i) :=
{ map_mul' := λ x y, by { ext, simp only [equiv.to_fun_as_coe, pi.mul_apply], },
  map_add' := λ m x, by { ext, simp only [equiv.to_fun_as_coe, pi.add_apply], },
  .. equiv.Pi_congr (equiv.refl ι) (λ i, (e i).to_equiv) }

def step7 [nontrivial R] [is_semisimple_module R R] :
  (Π (i : isomorphism_quot R R),
    matrix (quotient.class i) (quotient.class i) (module.End R i.out)) ≃+* module.End R R :=
(@ring_equiv.pi _ (λ i, module.End R (quotient.class i → i.out))
  (λ i, matrix (quotient.class i) (quotient.class i) (module.End R i.out)) _ _
  (λ i : isomorphism_quot R R, @equiv_to_matrix (quotient.class i) _ R i.out _ _ _)).symm.trans step6
