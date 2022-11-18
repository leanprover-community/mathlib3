import representation_theory.Rep
import representation_theory.fdRep

noncomputable theory

section basics

variables (R : Type*) (G : Type*) [monoid G]

-- example : G →* monoid_algebra R G := monoid_algebra.of R G

def monoid_algebra.of_conj_classes [semiring R] [fintype G] : conj_classes G → monoid_algebra R G :=
λ c, c.carrier.to_finite.to_finset.sum (monoid_algebra.of R G)

lemma of_conj_classes_eval [semiring R] [fintype G] {c : conj_classes G} {g : G}
  (h : g ∈ c.carrier) : monoid_algebra.of_conj_classes R G c g = (1 : R) :=
begin
  unfold monoid_algebra.of_conj_classes,
  rw finset.sum_apply',
  have h' : {g} ⊆ c.carrier.to_finite.to_finset,
    rwa [finset.singleton_subset_iff, set.finite.mem_to_finset],
  rw [←finset.sum_subset h', finset.sum_singleton],
  { unfold monoid_algebra.of,
    suffices : finsupp.single g 1 g = (1 : R), exact this,
    unfold finsupp.single,
    simp only [if_true, eq_self_iff_true, finsupp.coe_mk] },
  intros x h1 h2,
  { unfold monoid_algebra.of,
    suffices : finsupp.single x 1 g = (0 : R), exact this,
    unfold finsupp.single,
    simp only [ite_eq_right_iff, finsupp.coe_mk],
    intro h,
    exfalso,
    apply h2,
    rw [h, finset.mem_singleton] },
end

def monoid_algebra.center.of_conj_classes [comm_semiring R] [fintype G] :
  conj_classes G → subalgebra.center R (monoid_algebra R G) := λ c,
⟨ monoid_algebra.of_conj_classes R G c,
begin
  sorry,
end⟩

end basics

/-def basis.mk' {R M : Type*} [semiring R] [add_comm_monoid M] [module R M] {ι : Type*} (f : ι → M)
  (g : M → (ι →₀ R)) (h : ∀ x : M, )-/

namespace monoid_algebra
variables (R G : Type*) [comm_ring R] [group G] [fintype G] [nontrivial R]


lemma temp : linear_independent R (center.of_conj_classes R G) :=
begin
  rw linear_independent_iff',
  intros s f h c hc,
  let g : G := quot.out c,
  --set k := λ c, f c • center.of_conj_classes R G c,
  have : (s.sum (λ (i : conj_classes G), f i • center.of_conj_classes R G i)) g
  = (s.sum (λ (i : conj_classes G), (f i • center.of_conj_classes R G i) g ) ),
  have q := s.sum_apply g ((λ c, f c • center.of_conj_classes R G c)),
  sorry,
  have h' : s.sum (λ (i : conj_classes G), f i • center.of_conj_classes R G i) g = 0,
  { rw h, refl },
  rw this at h',
  let c' : finset (conj_classes G) := {c},
  have hc' : c' ⊆ s := finset.singleton_subset_iff.mpr hc,
  rw [←finset.sum_subset hc', finset.sum_singleton] at h',
  have : f c • center.of_conj_classes R G c g = 0 := h',
  have : (center.of_conj_classes R G c) g = 1,
  unfold center.of_conj_classes of_conj_classes,
end

/-def subalgebra_center.basis :
  basis (conj_classes G) R (subalgebra.center R (monoid_algebra R G)) :=
@basis.mk _ R _ (monoid_algebra.center.of_conj_classes R) _ _ _
begin
  rw linear_independent_iff',
  intros s f h c hc,
  let g : G := quot.out c,
  have h' : s.sum (λ (i : conj_classes G), f i • center.of_conj_classes R i) g = 0,
  { rw h, refl },
  have : (s.sum (λ (i : conj_classes G), f i • center.of_conj_classes R i)) g
  = (s.sum (λ (i : conj_classes G), (f i • center.of_conj_classes R i) g ) ),
  let i := s.sum_apply g ((λ c, f c • center.of_conj_classes R c)),

  sorry,
end
begin
  ext,
end-/

/-def subalgebra_center.basis :
  basis (conj_classes G) R (subalgebra.center R (monoid_algebra R G)) := ⟨linear_equiv.symm
{ to_fun := λ f, finsum (λ c, f c • center.of_conj_classes R c),
  map_add' := λ x y, begin
    rw ←finsum_add_distrib,
    apply congr_arg,
    ext1 c,
    apply add_smul,
    all_goals
    { apply set.finite.subset set.univ.to_finite (set.subset_univ _),
      apply_instance },
  end,
  map_smul' := λ r x, begin
    rw smul_finsum,
  end,
  inv_fun := begin
    intro x,
    apply finsupp.equiv_fun_on_fintype.symm.to_fun,
    refine @quotient.lift _ _ (is_conj.setoid _) (⇑x : G → R) (λ g h i, _),
    sorry,
    exact fintype.of_finite _,
  end,
  left_inv := _,
  right_inv := _ }⟩-/
/-
⟨{to_fun := begin
    intro x,
    apply finsupp.equiv_fun_on_fintype.symm.to_fun,
    refine @quotient.lift _ _ (is_conj.setoid _) (⇑x : G → R) (λ g h i, _),
    sorry,
    exact fintype.of_finite _,
  end,
  map_add' := λ x y, begin
    ext c,
    simp,
    sorry,
  end,
  map_smul' := λ r x, begin
    ext c,
    simp,
  end,
  inv_fun := λ f, (⊤ : set $ conj_classes G).to_finite.to_finset.sum (center.of_conj_classes R),
  left_inv := _,
  right_inv := _ }⟩-/

end monoid_algebra
