import algebraic_geometry.morphisms.basic


noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class quasi_compact (f : X ⟶ Y) : Prop :=
(is_compact_primage : ∀ U : set Y.carrier, is_open U → is_compact U → is_compact (f.1.base ⁻¹' U))

def quasi_compact.affine_property : affine_target_morphism_property :=
λ X Y f hf, compact_space X.carrier

lemma is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : finset { U : opens X.carrier | is_affine_open U }), U = ⋃ (i : s), i :=
begin
  classical,
  split,
  { rintro ⟨h₁, h₂⟩,
    obtain ⟨β, f, e, hf⟩ := (is_basis_affine_open X).open_eq_Union h₂,
    let hf' := λ i, (show is_open (f i), from (hf i).some_spec.2 ▸ (hf i).some.prop),
    obtain ⟨t, ht⟩ := h₁.elim_finite_subcover f hf' (by rw e),
    let f' : β → { U : opens X.carrier | is_affine_open U } :=
      λ i, ⟨⟨f i, hf' i⟩, by { convert (hf i).some_spec.1, ext1, exact (hf i).some_spec.2.symm }⟩,
    use t.image f',
    apply le_antisymm,
    { refine set.subset.trans ht _,
      simp only [set.Union_subset_iff, coe_coe],
      intros i hi,
      exact set.subset_Union (coe : t.image f' → set X.carrier) ⟨_, finset.mem_image_of_mem _ hi⟩ },
    { apply set.Union_subset,
      rintro ⟨i, hi⟩,
      obtain ⟨j, hj, rfl⟩ := finset.mem_image.mp hi,
      rw e,
      exact set.subset_Union f j } },
  { rintro ⟨s, rfl⟩,
    split,
    { convert @finset.compact_bUnion _ _ _ s.attach coe _,
      { ext, simpa },
      { exact λ i _, i.1.prop.is_compact } },
    { apply is_open_Union, rintro i, exact i.1.1.prop } },
end

lemma quasi_compact_iff_forall_affine : quasi_compact f ↔
  ∀ U : opens Y.carrier, is_affine_open U → is_compact (f.1.base ⁻¹' (U : set Y.carrier)) :=
begin
  rw quasi_compact_iff,
  refine ⟨λ H U hU, H U U.prop hU.is_compact, _⟩,
  intros H U hU hU',
  obtain ⟨S, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩,
  simp only [set.preimage_Union, subtype.val_eq_coe],
  convert S.compact_bUnion (λ i _, H i i.prop) using 1,
  exact set.Union_subtype _ _
end

lemma quasi_compact_iff_affine_property :
  quasi_compact f ↔ target_affine_locally quasi_compact.affine_property f :=
begin
  rw quasi_compact_iff_forall_affine,
  transitivity (∀ U : Y.affine_opens, is_compact (f.1.base ⁻¹' (U : set Y.carrier))),
  { exact ⟨λ h U, h U U.prop, λ h U hU, h ⟨U, hU⟩⟩ },
  apply forall_congr,
  exact λ _, is_compact_iff_compact_space,
end

lemma quasi_compact_iff_forall_affine : quasi_compact f ↔
  ∀ U : opens Y.carrier, is_affine_open U → is_compact (f.1.base ⁻¹' (U : set Y.carrier)) :=
begin
  rw quasi_compact_iff,
  refine ⟨λ H U hU, H U U.prop hU.is_compact, _⟩,
  intros H U hU hU',
  obtain ⟨S, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩,
  simp only [set.preimage_Union, subtype.val_eq_coe],
  convert S.compact_bUnion (λ i _, H i i.prop) using 1,
  exact set.Union_subtype _ _
end

lemma is_compact_basic_open (X : Scheme) {U : opens X.carrier} (hU : is_compact (U : set X.carrier))
  (f : X.presheaf.obj (op U)) : is_compact (X.basic_open f : set X.carrier) :=
begin
  classical,
  refine ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1,
  obtain ⟨s, hs⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.prop⟩,
  let g : s → X.affine_opens,
  { intro V,
    use V.1 ∩ X.basic_open f,
    have : V.1.1 ⟶ U,
    { apply hom_of_le, change _ ⊆ (U : set X.carrier), rw hs, exact set.subset_Union _ V },
    erw ← X.to_LocallyRingedSpace.to_RingedSpace.basic_open_res this.op,
    exact is_affine_open.basic_open_is_affine V.1.prop _ },
  use s.attach.image g,
  refine (set.inter_eq_right_iff_subset.mpr (RingedSpace.basic_open_subset _ _)).symm.trans _,
  rw [hs, set.Union_inter],
  apply le_antisymm; apply set.Union_subset,
  { intro i,
    refine set.subset.trans _
      (set.subset_Union _ (⟨_, finset.mem_image_of_mem g (s.mem_attach i)⟩ : s.attach.image g)),
    exact set.subset.rfl },
  { rintro ⟨i, hi⟩,
    obtain ⟨j : s, hj, rfl⟩ := finset.mem_image.mp hi,
    refine set.subset.trans _ (set.subset_Union _ j),
    exact set.subset.rfl }
end

lemma quasi_compact_of_affine_open_cover (S : set { U : opens Y.carrier | is_affine_open U })
  (hU₁ : (⋃ (i : S), (i : set Y.carrier)) = set.univ)
  (hU₂ : ∀ U : S, is_compact (f.1.base ⁻¹' (U : set Y.carrier))) : quasi_compact f :=
begin
  rw quasi_compact_iff_forall_affine,
  revert S,
  apply of_affine_open_cover (λ (U : opens Y.carrier), is_compact (f.val.base ⁻¹' U.1)),
  { intros U r hr hU,
    change is_compact ↑((opens.map f.val.base).obj (Y.basic_open r)),
    rw Scheme.preimage_basic_open f r,
    exact is_compact_basic_open X hU _ },
  { intros S hS,
    simp only [opens.supr_s, set.preimage_Union, subtype.val_eq_coe],
    exact compact_Union hS }
end

end algebraic_geometry
