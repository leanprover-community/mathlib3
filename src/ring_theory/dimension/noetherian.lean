import algebraic_geometry.prime_spectrum.noetherian
import topology.noetherian_space
import ring_theory.dimension.minimal_primes

variables {R : Type*} [comm_ring R]

open prime_spectrum topological_space

def irreducible_components (α : Type*) [topological_space α] : set (set α) :=
maximals (≤) { s : set α | is_irreducible s }

lemma noetherian_space.finite_irreducible_components
  {α : Type*} [topological_space α] [noetherian_space α] : (irreducible_components α).finite :=
begin
  classical,
  obtain ⟨S, hS₁, hS₂⟩ := noetherian_space.exists_finset_irreducible (⊤ : closeds α),
  suffices : irreducible_components α ⊆ coe '' (S : set $ closeds α),
  { exact set.finite.subset ((set.finite.intro infer_instance).image _) this },
  intros K hK,
  obtain ⟨z, hz, hz'⟩ : ∃ (z : set α) (H : z ∈ finset.image coe S), K ⊆ z,
  { convert is_irreducible_iff_sUnion_closed.mp
      hK.1 (S.image coe) _ _,
    { simp only [finset.mem_image, exists_prop, forall_exists_index, and_imp],
      rintro _ z hz rfl,
      exact z.2 },
    { exact (set.subset_univ _).trans ((congr_arg coe hS₂).trans $ by simp).subset } },
  obtain ⟨s, hs, e⟩ := finset.mem_image.mp hz,
  rw ← e at hz',
  refine ⟨s, hs, _⟩,
  symmetry,
  refine hK.2 (hS₁ ⟨s, hs⟩) _,
  simpa,
end

lemma is_closed_of_mem_irreducible_components {α : Type*} [topological_space α]
  (s ∈ irreducible_components α) : is_closed s :=
begin
  rw [← closure_eq_iff_is_closed, eq_comm],
  exact H.2 H.1.closure subset_closure,
end

lemma irreducible_components_eq_maximals_closed (α : Type*) [topological_space α] :
  irreducible_components α = maximals (≤) { s : set α | is_closed s ∧ is_irreducible s } :=
begin
  ext s,
  split,
  { intro H, exact ⟨⟨is_closed_of_mem_irreducible_components _ H, H.1⟩, λ x h e, H.2 h.2 e⟩ },
  { intro H, refine ⟨H.1.2, λ x h e, _⟩,
    have : s = closure x,
    { exact H.2 ⟨is_closed_closure, h.closure⟩ (e.trans subset_closure) },
    exact e.antisymm (has_le.le.trans_eq subset_closure this.symm) }
end

lemma image_maximals {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
  (t : set α)
  (h₁ : ∀ x y ∈ t, r x y ↔ s (f x) (f y))
  (h₂ : t.inj_on f) : f '' maximals r t = maximals s (f '' t) :=
begin
  ext,
  split,
  { rintros ⟨x, hx, rfl⟩,
    refine ⟨⟨_, hx.1, rfl⟩, _⟩,
    rintros _ ⟨y, hy, rfl⟩ e, congr, exact hx.2 hy ((h₁ _ hx.1 _ hy).mpr e) },
  { rintros ⟨⟨x, hx, rfl⟩, h⟩,
    refine ⟨x, ⟨hx, _⟩, rfl⟩,
    rintros y hy e,
    exact h₂ hx hy (h ⟨y, hy, rfl⟩ ((h₁ _ hx _ hy).mp e)) }
end

lemma zero_locus_minimal_primes :
  zero_locus ∘ coe '' minimal_primes R = irreducible_components (prime_spectrum R) :=
begin
  rw irreducible_components_eq_maximals_closed,
  convert image_maximals (zero_locus ∘ coe) _ _ _ using 2,
  { ext s,
    suffices : is_closed s ∧ is_irreducible s ↔ ∃ (J : ideal R), J.is_prime ∧ zero_locus ↑J = s,
    { simpa },
    split,
    { rintro ⟨h₁, h₂⟩,
      obtain ⟨J, e, rfl⟩ := (is_closed_iff_zero_locus_radical_ideal _).mp h₁,
      rw is_irreducible_zero_locus_iff_of_radical _ e at h₂,
      exact ⟨J, h₂, rfl⟩ },
    { rintros ⟨J, hJ, rfl⟩,
      rw [is_closed_iff_zero_locus_ideal, is_irreducible_zero_locus_iff],
      refine ⟨⟨_, rfl⟩, ideal.is_prime_radical hJ.is_primary⟩ } },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩, dsimp, rw [subset_zero_locus_iff_le_vanishing_ideal,
      vanishing_ideal_zero_locus_eq_radical, hJ.radical] },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩ e, apply_fun vanishing_ideal at e, dsimp at e,
    simp_rw [vanishing_ideal_zero_locus_eq_radical, hJ.radical, hK.radical] at e, exact e }
end

lemma vanishing_ideal_irreducible_components :
  vanishing_ideal '' irreducible_components (prime_spectrum R) = minimal_primes R :=
begin
  rw irreducible_components_eq_maximals_closed,
  change _ = maximals (≥) _,
  convert image_maximals _ _ _ _ using 2,
  { ext p,
    suffices : p.is_prime ↔ ∃ s, (is_closed s ∧ is_irreducible s) ∧ vanishing_ideal s = p,
    { simpa },
    split,
    { rintro hp,
      refine ⟨zero_locus p, ⟨is_closed_zero_locus _, _⟩, _⟩,
      { rwa is_irreducible_zero_locus_iff_of_radical _ hp.radical },
      { rw [vanishing_ideal_zero_locus_eq_radical, hp.radical] } },
    { rintros ⟨J, ⟨h₁, h₂⟩, rfl⟩,
      obtain ⟨J, e, rfl⟩ := (is_closed_iff_zero_locus_radical_ideal _).mp h₁,
      rwa [vanishing_ideal_zero_locus_eq_radical, ← is_irreducible_zero_locus_iff] } },
  { rintros J _ K ⟨hK, -⟩, dsimp, rw [← subset_zero_locus_iff_le_vanishing_ideal,
      zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr hK] },
  { rintros J ⟨hJ, -⟩ K ⟨hK, -⟩ e, apply_fun zero_locus ∘ (coe : ideal R → set R) at e, dsimp at e,
    simp_rw [zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr hK,
      closure_eq_iff_is_closed.mpr hJ] at e, exact e }
end

instance [H : is_noetherian_ring R] : noetherian_space (prime_spectrum R) :=
begin
  rw (noetherian_space_tfae $ prime_spectrum R).out 0 1,
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H,
  have : (closeds (prime_spectrum R))ᵒᵈ ↪o ideal R :=
  { to_fun := λ s, vanishing_ideal ↑(show closeds $ prime_spectrum R, from s),
    inj' := λ s t e, begin
      apply_fun zero_locus ∘ (coe : _ → set R) at e,
      dsimp at e,
      ext1,
      simpa only [zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr s.closed,
        closure_eq_iff_is_closed.mpr t.closed] using e,
    end,
    map_rel_iff' := λ s t, by { dsimp, rw [← subset_zero_locus_iff_le_vanishing_ideal,
      zero_locus_vanishing_ideal_eq_closure, closure_eq_iff_is_closed.mpr s.closed], refl } },
  exact this.dual.well_founded H
end

lemma minimal_primes_finite [is_noetherian_ring R] : (minimal_primes R).finite :=
begin
  rw ← vanishing_ideal_irreducible_components,
  exact noetherian_space.finite_irreducible_components.image _,
end

lemma ideal.minimal_primes_finite [is_noetherian_ring R] (I : ideal R) :
  I.minimal_primes.finite :=
begin
  rw ideal.minimal_primes_eq_comap,
  apply set.finite.image,
  exact minimal_primes_finite
end
