import topology.algebra.group
import group_theory.index
variables {G : Type*} [group G] [topological_space G] [topological_group G]

lemma nonempty_interior_of_is_open {U : subgroup G} (hU : is_open (U : set G)) :
  (interior (U : set G)).nonempty :=
by rw hU.interior_eq; exact ⟨1, U.one_mem⟩

variables (U : subgroup G)
open_locale classical
#check set.Union_image_preimage_sigma_mk_eq_self
lemma hmmm (hG : is_compact (@set.univ G)) {U : subgroup G} (hU : is_open (U : set G)) :
  ∃ t : finset (G ⧸ U), set.univ ⊆ ⋃ (x : G) (hx : x ∈ quotient_group.mk ⁻¹'
    (t : set (G ⧸ U))), (λ h : G, x * h) '' U :=
begin
  rcases compact_covered_by_mul_left_translates (by assumption) (nonempty_interior_of_is_open hU)
    with ⟨t, ht⟩,
  use finset.image (quotient_group.mk ∘ has_inv.inv) t,
  intros x hx,
  rcases set.mem_Union₂.1 (ht $ set.mem_univ x) with ⟨i, hti, hi⟩,
  rw set.mem_Union₂,
  use i⁻¹,
  split,
  simp only [finset.coe_image, set.mem_preimage, set.mem_image, finset.mem_coe],
  exact ⟨i, hti, rfl⟩,
  rw [set.image_mul_left, inv_inv],
  exact hi,
end
-- saying that if t₁U ∪ ... ∪ tₙU is everything, so is t₁gU ∪ ... ⋃ tₙgU
-- want to find tᵢ such that y ∈ tᵢgU; know gzw = y, want v ∈ U such that gzv = y
lemma mul_cover {G : Type*} [group G] {U t : set G} (g : G)
  (H : set.univ ⊆ ⋃ (x : G) (hx : x ∈ t), (λ h : G, x * h) '' U) :
  set.univ ⊆ ⋃ (x : G) (hx : x ∈ t), (λ h : G, (g * x) * h) '' U :=
begin
  intros y hy,
  rcases set.mem_Union.1 (H $ set.mem_univ (g⁻¹ * y)) with ⟨z, hz⟩,
  rcases set.mem_Union.1 hz with ⟨hzt, w, hwU, hw⟩,
  rw set.mem_Union₂,
  exact ⟨z, hzt, ⟨w, hwU, by { dsimp at hw ⊢, rw [mul_assoc, hw, mul_inv_cancel_left] }⟩⟩,
end

lemma mul_cover_finset {G : Type*} [group G] {U : set G} (t : finset G) (g : G)
  (H : set.univ ⊆ ⋃ (x : G) (hx : x ∈ t), (λ h : G, x * h) '' U) :
  set.univ ⊆ ⋃ (x : G) (hx : x ∈ t), (λ h : G, (g * x) * h) '' U :=
by convert mul_cover g H

lemma preimage_mul_one {G : Type*} [monoid G] (U : set G) :
  has_mul.mul 1 ⁻¹' U = U :=
begin
  ext,
  simp only [set.mem_preimage, one_mul],
end

lemma fucksake {G : Type*} [group G] (U : subgroup G) (i : G) :
  (⋃ (x : G) (hx : (quotient_group.mk x : G⧸U) = quotient_group.mk i), has_mul.mul (i⁻¹ * x) '' ↑U : set G)
   = U :=
begin
  ext,
  rw set.mem_Union₂,
  split,
  { rintros ⟨y, hyi, ⟨z, hzU, rfl⟩⟩,
    exact U.mul_mem (quotient_group.eq.1 hyi.symm) hzU },
  { intro hx,
    exact ⟨i, rfl, ⟨x, hx, by assoc_rw inv_mul_cancel_left⟩⟩ }
end

/-lemma umm {G : Type*} [group G] {U : subgroup G} {t : set (G ⧸ U)} (hne : U ≠ ⊤) :
  ∃ i : G, quotient_group.mk i ∈ t ∧ i ∈ U ∧
  U = (⋃ (x : G) (h : quotient_group.mk x ∈ t.erase (quotient_group.mk i)),
      has_mul.mul (i⁻¹ * x) '' (U : set G))ᶜ-/
lemma is_closed_and_index_ne_zero_of_open (hG : is_compact (@set.univ G))
  (hU : is_open (U : set G)) : is_closed (U : set G) ∧ U.index ≠ 0 :=
begin
  by_cases U = ⊤,
  { simp [h] },
  rcases hmmm hG hU with ⟨t, ht⟩,
  split,
  { have htU : ∃ i, quotient_group.mk i ∈ t ∧ i ∉ U := not_forall_not.1 (λ H,
    begin
      simp_rw not_and_not_right at H,
      refine h _,
      rw eq_top_iff,
      intros x hx,
      rcases set.mem_Union₂.1 (ht $ set.mem_univ x) with ⟨g, hgt, ⟨y, hyU, rfl⟩⟩,
      exact U.mul_mem (H g hgt) hyU,
    end),
    cases htU with i hi,
    have h1 := mul_cover i⁻¹ ht,
    rw [←finset.insert_erase hi.1, finset.coe_insert, ←set.union_singleton, set.preimage_union,
      set.bUnion_union] at ht h1,
    simp only [set.mem_preimage, finset.mem_coe, set.mem_singleton_iff] at ht h1,
    rw fucksake at h1,
    have h2 : (U : set G) = (⋃ (x : G) (h : quotient_group.mk x ∈ t.erase (quotient_group.mk i)),
      has_mul.mul (i⁻¹ * x) '' (U : set G))ᶜ,
    begin
      rw set.univ_subset_iff at ht h1,
      rw [set.compl_eq_univ_diff, ←h1, set.union_diff_cancel_left],
      rintros x ⟨hx1, hx2⟩,
      rcases set.mem_Union₂.1 hx1 with ⟨w, hw, ⟨y, z, hy⟩⟩,
      refine (finset.mem_erase.1 hw).1 _,
      rw quotient_group.eq',
      suffices : w⁻¹ * i = y * x⁻¹,
      begin
        rw this,
        exact U.mul_mem z (U.inv_mem hx2),
      end,
      rw ←hy,
      norm_num,
    end,
    rw [h2, is_closed_compl_iff],
    refine is_open_bUnion _,
    intros g hg,
    exact is_open.left_coset hU (i⁻¹ * g) },
  { have e : t ≃ G ⧸ U :=
    equiv.of_bijective coe ⟨by intros; ext,
    begin
      intro g,
      refine quotient_group.induction_on' g (λ h, _),
      rcases set.mem_Union₂.1 (ht (set.mem_univ h)) with ⟨w, hw, ⟨y, z, hy⟩⟩,
      use ⟨w, hw⟩,
      rw ←hy,
      dsimp,
      rwa [quotient_group.eq, inv_mul_cancel_left],
    end⟩,
    convert subgroup.index_ne_zero_of_fintype,
    exact fintype.of_equiv _ e }
end

theorem is_open_of_is_closed_and_index_ne_zero (hU : is_closed (U : set G) ∧ U.index ≠ 0) :
  is_open (U : set G) :=
begin
  by_cases U = ⊤,
  { simp [h] },
  { have : (U : set G) = (⋃ (i : G ⧸ U) (hi : i ≠ (1 : G)),
      has_mul.mul (quotient.out' i) '' (U : set G))ᶜ,
    begin
  -- this must be wasting energy
      rw set.compl_Union₂,
      ext,
      rw set.mem_Inter₂,
      split,
      { intros hx i,
        refine quotient_group.induction_on' i (λ i, _),
        rintros hi ⟨y, hyU, hy⟩,
        refine hi _,
        rw ←eq_mul_inv_iff_mul_eq at hy,
        suffices : (i : G ⧸ U) = (x * y⁻¹ : G),
        begin
          rw [this, quotient_group.eq, mul_one, mul_inv_rev, inv_inv],
          exact U.mul_mem hyU (U.inv_mem hx)
        end,
        rw ←hy,
        exact (quotient.out_eq' _).symm, },
      { intro hx,
        have := hx x,
        contrapose! this,
        split,
        { intro hq,
          refine this _,
          have := quotient_group.eq.1 hq.symm,
          rwa [inv_one, one_mul] at this },
        { intro H,
          rw ←set.image_compl_eq at H,
          rcases H with ⟨y, hyU, hy⟩,
          refine set.mem_compl hyU _,
          rw ←eq_mul_inv_iff_mul_eq at hy,
          have : (_ : G ⧸ U) = _ := congr_arg quotient_group.mk hy,
          rw quotient_group.out_eq' at this,
          have h2 := quotient_group.eq.1 this,
          rw inv_mul_cancel_left at h2,
          exact U.inv_mem_iff.1 h2,
          exact group.mul_left_bijective _ } },
    end,
    rw [←is_closed_compl_iff, this, compl_compl],
    refine is_closed_bUnion _ _,
    { haveI := subgroup.fintype_of_index_ne_zero hU.2,
      constructor,
      apply_instance },
    { intros i hi,
      exact is_closed.left_coset hU.1 _ }}
end

lemma is_open_iff_is_closed_and_index_ne_zero (hG : is_compact (@set.univ G))
  (U : subgroup G) : is_open (U : set G) ↔ is_closed (U : set G) ∧ U.index ≠ 0 :=
⟨is_closed_and_index_ne_zero_of_open U hG, is_open_of_is_closed_and_index_ne_zero U⟩
