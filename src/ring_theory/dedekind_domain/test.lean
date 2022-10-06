import ring_theory.dedekind_domain.ideal


section

variables {R S : Type*} [comm_ring R] [comm_ring S]
variables [algebra R S]
variable (R)

/-- Let `S / R` be a ring extension and `x : S`, then the conductor of R[x] is the
biggest ideal of `S` contained in `R[x]`. -/
def conductor (x : S) : ideal S :=
{ carrier := {a | ∀ (b : S), a * b ∈ algebra.adjoin R ({x} : set S)},
  zero_mem' := λ b, by simpa only [zero_mul] using subalgebra.zero_mem _,
  add_mem' := λ a b ha hb c, by simpa only [add_mul] using subalgebra.add_mem _ (ha c) (hb c),
  smul_mem' := λ c a ha b, by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b) }

variables {R}

lemma mem_adjoin_of_mem_conductor {x y : S} (hy : y ∈ conductor R x) :
  y ∈ algebra.adjoin R ({x} : set S) :=
by simpa only [mul_one] using hy 1

lemma conductor_eq_of_eq {x y : S} (h : (algebra.adjoin R ({x} : set S) : set S) =
  algebra.adjoin R ({y} : set S)) : conductor R x = conductor R y :=
ideal.ext (λ a, ⟨λ H b, by {rw set.ext_iff at h, rw ← set_like.mem_coe, rw ← h, exact H b, } , λ H b,
    by {rw set.ext_iff at h, rw ← set_like.mem_coe, rw h, exact H b, }⟩ )


lemma conductor_subset_adjoin {x : S} : (conductor R x : set S) ⊆ algebra.adjoin R ({x} : set S) :=
λ y, mem_adjoin_of_mem_conductor

lemma mem_conductor_iff {x y : S} :
  y ∈ conductor R x ↔ ∀ (b : S), y * b ∈ algebra.adjoin R ({x} : set S) :=
⟨λ h, h, λ h, h⟩

end

variables {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] {I : ideal R}

/-- This technical lemma tell us that if `C` is the conductor of `R[α]` and `I` is an ideal of R
  then `p * (I * S) ⊆ I*R[α]` for any `p` in `C ∩ R` (this should be generalized to `p ∈ C`) -/
lemma tricky_result {I : ideal R} {x : S} (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x) {p : R} (hp : p ∈ ideal.comap (algebra_map R S) (conductor R x))
  {z : S} (hz : z ∈ algebra.adjoin R ({x} : set S))
  {hz' : z ∈ (I.map (algebra_map R S))} :
  (algebra_map R S p)*z ∈ algebra_map (algebra.adjoin R ({x} : set S)) S
    '' ↑(I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) :=
begin
  rw [ideal.map, ideal.span, finsupp.mem_span_image_iff_total] at hz',
  obtain ⟨l, H, H'⟩ := hz',
  rw finsupp.total_apply at H',
  rw [← H', mul_comm, finsupp.sum_mul],
  have test2 : ∀ {a : R}, a ∈ I → (l a • (algebra_map R S a) * (algebra_map R S p) ) ∈ (algebra_map
   (algebra.adjoin R ({x} : set S)) S) '' (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))),
  { intros a ha,
    rw [algebra.id.smul_eq_mul, mul_assoc, mul_comm, mul_assoc, set.mem_image],
    refine exists.intro (algebra_map R (algebra.adjoin R ({x} : set S)) a * ⟨l a * algebra_map R S
      p, show l a * algebra_map R S p ∈ (algebra.adjoin R ({x} : set S)), from _ ⟩) _,
    { rw mul_comm,
      exact mem_conductor_iff.mp (ideal.mem_comap.mp hp) _ },
    refine ⟨_, by simpa only [map_mul, mul_comm (algebra_map R S p) (l a)]⟩,
    rw mul_comm,
    apply ideal.mul_mem_left (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) _
      (ideal.mem_map_of_mem _ ha) },
  refine finset.sum_induction _ (λ u, u ∈ (algebra_map (algebra.adjoin R ({x} : set S)) S) ''
    (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))))
    (λ a b ha hb, _) _ _,
  obtain ⟨z, hz, rfl⟩ := (set.mem_image _ _ _).mp ha,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image _ _ _).mp hb,
  rw [← ring_hom.map_add, set.mem_image],
  exact exists.intro (z + y)
    ⟨ideal.add_mem (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) hz hy, rfl⟩,
  { refine (set.mem_image _ _ _).mpr (exists.intro 0 ⟨ideal.zero_mem (I.map (algebra_map R
    (algebra.adjoin R ({x} : set S)))), (ring_hom.map_zero _)⟩) },
  { intros y hy,
    exact test2 ((finsupp.mem_supported _ l).mp H hy) },
end


/-- A technical result telling us us that `(I*S) ∩ R[α] = I*R[α]` -/
lemma test (I : ideal R) (x : S)
  (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x)
  (h_alg : function.injective (algebra_map (algebra.adjoin R ( {x} : set S)) S)):
  (I.map (algebra_map R S)).comap
  (algebra_map (algebra.adjoin R ( {x} : set S)) S) =
  I.map (algebra_map R (algebra.adjoin R ( {x} : set S))) :=
begin
  apply le_antisymm,
  swap,
  { have : algebra_map R S = (algebra_map (algebra.adjoin R ( {x} : set S)) S).comp
      (algebra_map R (algebra.adjoin R ( {x} : set S))) := by { ext, refl },
    rw [this, ← ideal.map_map],
    apply ideal.le_comap_map },
  { intros y hy,
    obtain ⟨z, hz⟩ := y,
    obtain ⟨p, hp, q, hq, hpq⟩ := submodule.mem_sup.mp ((ideal.eq_top_iff_one _).mp hx),
    have temp : (algebra_map R S p)*z + (algebra_map R S q)*z = z,
    { simp only [←add_mul, ←ring_hom.map_add (algebra_map R S), hpq, map_one, one_mul] },
    suffices : z ∈ algebra_map (algebra.adjoin R ({x} : set S)) S '' (I.map (algebra_map R
      (algebra.adjoin R ({x} : set S)))) ↔ (⟨z, hz⟩ : (algebra.adjoin R ({x} : set S)))
      ∈ I.map (algebra_map R (algebra.adjoin R ({x} : set S))),
    { rw [← this, ← temp],
      obtain ⟨a, ha⟩ := (set.mem_image _ _ _).mp (tricky_result hx hx' hp hz),
      use a + (algebra_map R (algebra.adjoin R ({x} : set S)) q) * ⟨z, hz⟩,
      refine ⟨ ideal.add_mem (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) ha.left _,
        by simpa only [ha.right, map_add, map_mul, add_right_inj] ⟩,
      { rw mul_comm,
        exact ideal.mul_mem_left (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) _
          (ideal.mem_map_of_mem _ hq) },
      rwa ideal.mem_comap at hy },
    refine ⟨ λ h, _, λ h, (set.mem_image _ _ _).mpr (exists.intro ⟨z, hz⟩ ⟨by simp [h], rfl⟩ ) ⟩,
    { obtain ⟨x₁, hx₁, hx₂⟩ := (set.mem_image _ _ _).mp h,
      have : x₁ = ⟨z, hz⟩,
      { apply h_alg,
        simpa [hx₂], },
      rwa ← this }  }
end

lemma ideal.quotient.lift_surjective_of_surjective (I : ideal R) (f : R →+* S)
  (H : ∀ (a : R), a ∈ I → f a = 0) (hf : function.surjective f) :
    function.surjective (ideal.quotient.lift I f H) :=
begin
  intro y,
  obtain ⟨x, rfl⟩ := hf y,
  use ideal.quotient.mk I x,
  simp only [ideal.quotient.lift_mk],
end

lemma ideal.quotient.lift_injective_of_ker_le_ideal (I : ideal R) (f : R →+* S)
  (H : ∀ (a : R), a ∈ I → f a = 0) (hI : f.ker ≤ I) :
  function.injective (ideal.quotient.lift I f H) :=
begin
    rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_bot_iff_eq_zero],
    intros u hu,
    obtain ⟨v, rfl⟩ := ideal.quotient.mk_surjective u,
    rw ideal.quotient.lift_mk at hu,
    rw [ideal.quotient.eq_zero_iff_mem],
    exact hI ((ring_hom.mem_ker f).mpr hu),
end

noncomputable def quot_adjoin_equiv_quot_map (x : S) (hx : (conductor R x).comap
  (algebra_map R S) ⊔ I = ⊤) (hx' : is_integral R x)
  (h_alg : function.injective (algebra_map (algebra.adjoin R ( {x} : set S)) S)) :
  (algebra.adjoin R ( {x} : set S)) ⧸ (I.map (algebra_map R (algebra.adjoin R ( {x} : set S))))
    ≃+* S ⧸ (I.map (algebra_map R S : R →+* S)) :=
ring_equiv.of_bijective (ideal.quotient.lift (I.map (algebra_map R (algebra.adjoin R ( {x} : set S))))
  (((I.map (algebra_map R S : R →+* S))^.quotient.mk).comp
  (algebra_map (algebra.adjoin R ( {x} : set S)) S : (algebra.adjoin R ( {x} : set S)) →+* S))
  (λ r hr, by {
    have : algebra_map R S = (algebra_map (algebra.adjoin R ( {x} : set S)) S).comp
    (algebra_map R (algebra.adjoin R ( {x} : set S))) := by ext ; refl,
    rw [ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem, this, ← ideal.map_map],
    exact ideal.mem_map_of_mem _ hr } ))
begin
  split,
  { refine ideal.quotient.lift_injective_of_ker_le_ideal _ _ _ (λ u hu, _),
    rwa [ring_hom.mem_ker, ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem,
      ← ideal.mem_comap, test I x hx hx' h_alg] at hu },
  { apply ideal.quotient.lift_surjective_of_surjective,
    intro y,
    obtain ⟨z, hz⟩ := ideal.quotient.mk_surjective y,
    have : z ∈ conductor R x ⊔ (I.map (algebra_map R S : R →+* S)),
    { suffices : conductor R x ⊔ (I.map (algebra_map R S : R →+* S)) = ⊤,
      { simp [this] },
      rw ideal.eq_top_iff_one at hx ⊢,
      replace hx := ideal.mem_map_of_mem (algebra_map R S) hx,
      rw [ideal.map_sup, ring_hom.map_one] at hx,
      exact (sup_le_sup (show  ((conductor R x).comap (algebra_map R S)).map (algebra_map R S) ≤
        conductor R x, from ideal.map_comap_le) (le_refl (I.map (algebra_map R S)))) hx },
    rw [← ideal.mem_quotient_iff_mem_sup, hz, ideal.mem_map_iff_of_surjective] at this,
    obtain ⟨u, hu, hu'⟩ := this,
    use ⟨u, conductor_subset_adjoin hu⟩,
    simpa only [← hu'],
    { exact ideal.quotient.mk_surjective } }

end
