import field_theory.is_alg_closed.basic
import field_theory.perfect_closure
import ring_theory.witt_vector.domain

noncomputable theory

variables (p : ℕ) [fact p.prime]
variables (k : Type*) [field k] [char_p k p] [is_alg_closed k]

/-- A field is perfect if Frobenius is surjective -/
def perfect_ring.of_surjective (k : Type*) [field k] [char_p k p]
  (h : function.surjective $ frobenius k p) :
  perfect_ring k p :=
{ pth_root' := function.surj_inv h,
  frobenius_pth_root' := function.surj_inv_eq h,
  pth_root_frobenius' := λ x, (frobenius k p).injective $ function.surj_inv_eq h _ }

-- an algebraically closed field is perfect, many google hits, maybe somewhere in mathlib?
instance is_alg_closed.perfect_ring : perfect_ring k p :=
perfect_ring.of_surjective p k $ λ x, is_alg_closed.exists_pow_nat_eq _ $ fact.out _

local notation `𝕎` := witt_vector p
local notation `K` := fraction_ring (𝕎 k)

lemma witt_vector.frobenius_bijective (R : Type*) [comm_ring R] [char_p R p] [perfect_ring R p] :
  function.bijective (@witt_vector.frobenius p R _ _) :=
begin
  rw witt_vector.frobenius_eq_map_frobenius,
  exact ⟨witt_vector.map_injective _ (frobenius_equiv R p).injective,
    witt_vector.map_surjective _ (frobenius_equiv R p).surjective⟩,
end

local notation `φ` := is_fraction_ring.field_equiv_of_ring_equiv
  (ring_equiv.of_bijective _ (witt_vector.frobenius_bijective p k))

lemma split (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b :=
begin
  obtain ⟨m, c, hc, hcm⟩ := witt_vector.verschiebung_nonzero ha,
  obtain ⟨b, rfl⟩ := (witt_vector.frobenius_bijective p k).surjective.iterate m c,
  rw witt_vector.iterate_frobenius_coeff at hc,
  -- have := ((frobenius_equiv k p).injective.iterate m).ne,
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b,
  simp at this,
  rw ← this at hcm,
  refine ⟨m, b, _, _⟩,
  { sorry },
  { sorry },
end

-- lemma witt_vector.is_Hausdorff : is_Hausdorff (𝕎 k)

lemma important_aux {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ (b : 𝕎 k) (hb : b ≠ 0), witt_vector.frobenius b * a₁ = b * a₂ :=
sorry

lemma important {a : fraction_ring (𝕎 k)} (ha : a ≠ 0) :
  ∃ (b : fraction_ring (𝕎 k)) (hb : b ≠ 0) (m : ℤ), φ b * a = p ^ m * b :=
begin
  refine localization.induction_on a _,
  rintros ⟨r, q, hq⟩,
  rw mem_non_zero_divisors_iff_ne_zero at hq,
  have : r ≠ 0 := sorry,
  obtain ⟨m, r', hr', rfl⟩ := split p k r this,
  obtain ⟨n, q', hq', rfl⟩ := split p k q hq,
  obtain ⟨b, hb, hb⟩ := important_aux p k hr' hq',
  refine ⟨algebra_map (𝕎 k) _ b, _, m - n, _⟩,
  { sorry },
  simp [is_fraction_ring.field_equiv_of_ring_equiv],
  suffices :
  witt_vector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q') ,
  { -- apply `algebra_map` to both sides and divide
    sorry },
  have H := congr_arg (λ x : 𝕎 k, x * p ^ m * p ^ n) hb,
  dsimp at H,
  refine (eq.trans _ H).trans _; ring
end
