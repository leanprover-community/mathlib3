import number_theory.number_field.canonical_embedding

open_locale classical

section log_embedding

open number_field fintype number_field.infinite_place finite_dimensional

variables (K : Type*) [field K]

localized "notation (name := ring_of_integers)
  `𝓞` := number_field.ring_of_integers" in log_embedding

def number_field.units : subgroup Kˣ :=
{ carrier := { x : Kˣ | (x : K) ∈ 𝓞 K ∧ (x⁻¹ : K) ∈ 𝓞 K },
  mul_mem' :=
  begin
    rintros x y  ⟨hx, hxi⟩ ⟨hy, hyi⟩,
    split,
    exact is_integral_mul hx hy,
    rw [← units.coe_inv, mul_inv, units.coe_mul, units.coe_inv, units.coe_inv],
    exact is_integral_mul hxi hyi,
  end,
  one_mem' := by simpa only [set.mem_set_of_eq, units.coe_one, inv_one, and_self]
    using is_integral_one,
  inv_mem' :=
  begin
    intros x hx,
    simp only [set.mem_set_of_eq, units.coe_inv, inv_inv, hx.1, hx.2, and_self],
  end }

noncomputable def log_embedding : Kˣ → (infinite_place K → ℝ) :=
λ x w, real.log (w x)

localized "notation (name := units) `𝓤` := number_field.units"
  in log_embedding

namespace number_field.log_embedding

variable {K}

lemma map_one : log_embedding K 1 = 0 :=
by simpa only [log_embedding, infinite_place.map_one, real.log_one, units.coe_one, coe_coe,
  algebra_map.coe_one]

lemma map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, infinite_place.map_mul, real.log_mul, units.coe_mul, ne.def,
  infinite_place.eq_zero, units.ne_zero, not_false_iff]

lemma map_inv (x : Kˣ) : log_embedding K x⁻¹ = - log_embedding K x :=
by simpa [log_embedding, infinite_place.map_inv, real.log_inv]

variable (K)

def units.add_subgroup : add_subgroup (infinite_place K → ℝ) :=
{ carrier := (log_embedding K) '' (𝓤 K),
  add_mem' :=
  begin
    rintros _ _ ⟨x, ⟨hx, rfl⟩⟩ ⟨y, ⟨hy, rfl⟩⟩,
    refine ⟨x * y, ⟨_, map_mul x y⟩⟩,
    rw set_like.mem_coe at hx hy ⊢,
    exact subgroup.mul_mem _ hx hy,
  end,
  zero_mem' :=
  begin
    refine ⟨1, ⟨_, map_one⟩⟩ ,
    rw set_like.mem_coe,
    exact subgroup.one_mem _,
  end,
  neg_mem' :=
  begin
    rintros _ ⟨x, ⟨⟨hx, hxi⟩, rfl⟩⟩,
    refine ⟨x⁻¹, ⟨⟨_, _⟩, map_inv x⟩⟩,
    { rwa units.coe_inv, },
    { rwa [units.coe_inv, inv_inv], },
  end }

localized "notation (name := lattice) `Λ` := number_field.log_embedding.units.add_subgroup"
  in log_embedding

lemma units.eq_zero (x : 𝓤 K) : log_embedding K x = 0 ↔ ∃ (n : ℕ) (H : 1 ≤ n), x^n = 1 := by sorry

lemma units.discrete : discrete_topology (Λ K) := by sorry

lemma units.free_module : module.free ℤ (Λ K) := by sorry

lemma units.rank_le [number_field K] : finrank ℤ (Λ K) ≤  card (infinite_place K) - 1 := by sorry

lemma units.le_rank [number_field K] : card (infinite_place K) - 1 ≤ finrank ℤ (Λ K)  := by sorry

lemma units.rank [number_field K] :
  finrank ℤ (Λ K) = card (infinite_place K) - 1 := le_antisymm (units.rank_le K) (units.le_rank K)

end number_field.log_embedding

end log_embedding
