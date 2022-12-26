import number_theory.number_field.canonical_embedding
import group_theory.torsion

section torsion

variables {G : Type*}

@[to_additive]
lemma comm_monoid.mem_torsion [comm_monoid G] (g : G) :
  g ∈ comm_monoid.torsion G ↔ is_of_fin_order g := iff.rfl

@[to_additive]
lemma comm_group.mem_torsion [comm_group G] (g : G) :
  g ∈ comm_group.torsion G ↔ is_of_fin_order g := iff.rfl

end torsion

open_locale classical

variables (K : Type*) [field K]

localized "notation `𝓤`K := (number_field.ring_of_integers K)ˣ" in units

namespace number_field.unit

section to_field_unit

open number_field

def to_field_unit : (𝓤 K) →* Kˣ := units.map (algebra_map (ring_of_integers K) K)

lemma injective.to_field_unit : function.injective (to_field_unit K) :=
begin
  intros x y hxy,
  rw units.ext_iff,
  have t1 := congr_arg (coe : Kˣ → K) hxy,
  simp_rw [to_field_unit, units.coe_map] at t1,
  exact (no_zero_smul_divisors.algebra_map_injective (ring_of_integers K) K) t1,
end

lemma ext.to_field_unit (x y : (𝓤 K)) :
  x = y ↔ to_field_unit K x = to_field_unit K y :=
⟨λ h, congr_arg (to_field_unit K) h, λ h, (injective.to_field_unit K) h⟩

instance : has_coe (𝓤 K) Kˣ := ⟨to_field_unit K⟩

lemma coe_injective : function.injective (coe : (𝓤 K) → Kˣ) :=
injective.to_field_unit K

@[simp]
lemma coe_ext (x y : (𝓤 K)) : x = y ↔ (x : Kˣ) = (y : Kˣ) :=
ext.to_field_unit K _ _

@[simp]
lemma coe_inv (x : (𝓤 K)) : ((x⁻¹ : (𝓤 K)): Kˣ) = (x : Kˣ)⁻¹ :=
map_inv (to_field_unit K) _

@[simp]
lemma coe_pow (x : (𝓤 K)) (n : ℕ) : ((x ^ n : (𝓤 K)) : Kˣ) = (x : Kˣ) ^ n :=
map_pow (to_field_unit K) _ _

def unit_subgroup : subgroup Kˣ := monoid_hom.range (to_field_unit K)

lemma mem_unit_subgroup (x : Kˣ) :
  x ∈ unit_subgroup K ↔ is_integral ℤ (x : K) ∧ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨x, rfl⟩,
    exact ⟨x.val.2, by { convert x.inv.2, rw ← units.coe_inv, refl, }⟩ },
  { exact λ ⟨hx, hxi⟩, ⟨⟨⟨x.1, hx⟩, ⟨x.1⁻¹, hxi⟩,
      by { simpa only [units.val_eq_coe, units.mul_inv', mul_mem_class.mk_mul_mk], },
      by { simpa only [units.val_eq_coe, units.inv_mul', mul_mem_class.mk_mul_mk], }⟩,
      by { simpa only [units.ext_iff], }⟩, },
end

end to_field_unit

section roots_of_unity

open number_field number_field.infinite_place

def roots_of_unity : subgroup 𝓤 K := comm_group.torsion (𝓤 K)

lemma mem_roots_of_unity [number_field K] (x : (𝓤 K)) :
  x ∈ roots_of_unity K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw ( eq_iff_eq x 1 : (∀ w : infinite_place K, w x = 1) ↔ ∀ (φ : K →+* ℂ), ‖φ (x : K)‖ = 1),
  rw [roots_of_unity, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  split,
  { rintros ⟨n, ⟨hn1, hn2⟩⟩ φ,
    lift n to ℕ+ using hn1,
    rw [coe_ext, coe_pow, units.ext_iff, units.coe_pow] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [coe_ext, coe_pow, units.ext_iff, units.coe_pow], }⟩⟩},
end

lemma finite_roots_of_unity [number_field K]: finite (roots_of_unity K) :=
begin
  suffices : ((coe : (𝓤 K) → K) '' { x : (𝓤 K) | x ∈ (roots_of_unity K )}).finite,
  { refine set.finite_coe_iff.mpr (set.finite.of_finite_image this (set.inj_on_of_injective _ _)),
    rw ( rfl : coe = (coe : Kˣ → K) ∘ (coe : (𝓤 K) → Kˣ)),
    exact (function.injective.of_comp_iff units.ext _).mpr (unit.coe_injective K), },
  refine (embeddings.finite_of_norm_le K ℂ 1).subset _,
  rintros a ⟨⟨u, _, _, _⟩, ⟨hu, rfl⟩⟩,
  split,
  { exact u.2, },
  { rw ← le_iff_le,
    convert λ w, le_of_eq (((mem_roots_of_unity K _).mp hu) w) using 1, },
end

lemma roots_of_unity_cyclic [number_field K]: is_cyclic (roots_of_unity K) :=
begin
  haveI := finite_roots_of_unity K,
  exact subgroup_units_cyclic _,
end

end roots_of_unity

end number_field.unit

noncomputable def number_field.log_embedding : Kˣ → (number_field.infinite_place K → ℝ) :=
λ x w, real.log (w x)

namespace number_field.log_embedding

open number_field fintype number_field.infinite_place number_field.unit finite_dimensional

lemma map_one : log_embedding K 1 = 0 :=
by simpa only [log_embedding, map_one, real.log_one, units.coe_one, coe_coe, algebra_map.coe_one]

lemma map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, map_mul, real.log_mul, units.coe_mul, ne.def, map_eq_zero,
  units.ne_zero, not_false_iff]

lemma map_inv (x : Kˣ) : log_embedding K x⁻¹ = - log_embedding K x :=
by simpa [log_embedding, map_inv, real.log_inv]

lemma eq_zero_iff (x : Kˣ) :
  log_embedding K x = 0 ↔ (∀ w : infinite_place K, w x = 1) :=
begin
  dsimp only [log_embedding],
  rw function.funext_iff,
  simp_rw pi.zero_apply,
  split,
  { exact λ h w, real.eq_one_of_pos_of_log_eq_zero ((w.pos_iff x).mpr (units.ne_zero x)) (h w), },
  { intros h w,
    simp [← coe_coe, h w, real.log_one], },
end

lemma nnnorm_eq [number_field K] (x : Kˣ) :
  ‖log_embedding K x‖₊ = finset.univ.sup (λ w : infinite_place K, ‖real.log (w x)‖₊ ) :=
by simp only [pi.nnnorm_def, log_embedding]

lemma le_of_le [number_field K] (x : Kˣ) (r : ℝ) :
  ‖log_embedding K x‖ ≤ r ↔ ∀ w : infinite_place K, real.exp (- r) ≤ w x ∧ w x ≤ real.exp r :=
begin
   obtain hr | hr := lt_or_le r 0,
  { split,
    { intro h, exfalso,
      exact (not_le.mpr (lt_of_le_of_lt h hr)) (norm_nonneg _), },
    { intro h, exfalso,
      obtain ⟨w⟩ := infinite_place.nonempty K,
      have := real.exp_le_exp.mp (le_trans (h w).1 (h w).2),
      linarith, }},
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left, ← nnreal.coe_le_coe, coe_nnnorm, real.norm_eq_abs, abs_le],
    split,
    { intros h w,
      specialize h w,
      rwa [← real.log_le_iff_le_exp, ← real.le_log_iff_exp_le],
      all_goals { exact (infinite_place.pos_iff w x).mpr (units.ne_zero x), }},
    { intros h w,
      specialize h w,
      rwa [real.log_le_iff_le_exp, real.le_log_iff_exp_le],
      all_goals { exact (infinite_place.pos_iff w x).mpr (units.ne_zero x), }}}
end

localized "notation `E` := (infinite_place K → ℝ)" in units

def unit_lattice : add_subgroup (E) :=
{ carrier := (log_embedding K) '' (unit_subgroup K),
  add_mem' :=
  begin
    rintros _ _ ⟨u, ⟨hu, rfl⟩⟩ ⟨v, ⟨hv, rfl⟩⟩,
    exact ⟨u * v, ⟨(unit_subgroup K).mul_mem hu hv, map_mul K u v⟩⟩,
  end,
  zero_mem' := ⟨1, ⟨(unit_subgroup K).one_mem, map_one K⟩⟩,
  neg_mem' :=
  begin
    rintros _ ⟨u, ⟨hu, rfl⟩⟩,
    refine ⟨u⁻¹, ⟨(unit_subgroup K).inv_mem hu, map_inv K u⟩⟩,
  end }

localized "notation `Λ` := (unit_lattice K)" in units

lemma unit_lattice.kernel [number_field K] (x : 𝓤 K) :
  log_embedding K x = 0 ↔ x ∈ roots_of_unity K :=
by { rw [eq_zero_iff, mem_roots_of_unity K x], refl, }

lemma unit_lattice.discrete [number_field K]: discrete_topology Λ :=
begin
  suffices : (metric.closed_ball (0 : Λ) 1).finite,
  { exact
    add_group.discrete_of_finite_ball (by norm_num) (this.subset metric.ball_subset_closed_ball), },
  let A := {x : Kˣ | is_integral ℤ (x : K) ∧ ∀ φ : (K →+* ℂ), ‖φ x‖ ≤ real.exp 1},
  have t1 : A.finite,
  { suffices : ((coe : Kˣ → K) '' A).finite,
    { exact this.of_finite_image (set.inj_on_of_injective units.ext _), },
    refine set.finite.subset (embeddings.finite_of_norm_le K ℂ (real.exp 1)) _,
    rintros _ ⟨u, ⟨hu, rfl⟩⟩,
    rw set.mem_set_of_eq,
    exact hu, },
  have t2 : ((log_embedding K) '' A).finite := set.finite.image _ t1,
  suffices : ((coe : Λ → E)'' (metric.closed_ball 0 1)).finite,
  { exact this.of_finite_image (set.inj_on_of_injective (subtype.val_injective) _), },
  refine t2.subset _,
  rintros _ ⟨⟨_, ⟨x, ⟨hx, rfl⟩⟩⟩, ⟨hu, rfl⟩⟩,
  use x,
  split,
  { split,
    { rw set_like.mem_coe at hx,
      rw mem_unit_subgroup at hx,
      exact hx.1, },
    { intro φ,
      rw metric.mem_closed_ball at hu,
      rw dist_zero_right at hu,
      rw add_subgroup.coe_norm at hu,
      rw subtype.coe_mk at hu,
      rw le_of_le at hu,
      specialize hu (mk φ),
      rw apply at hu,
      exact hu.right, }},
  { refl, },
end

lemma unit_lattice.free_module : module.free ℤ (unit_lattice K) := by sorry

lemma unit_lattice.rank_le [number_field K] :
  finrank ℤ (unit_lattice K) ≤  card (infinite_place K) - 1 := by sorry

lemma unit_lattice.le_rank [number_field K] :
  card (infinite_place K) - 1 ≤ finrank ℤ (unit_lattice K)  := by sorry

lemma unit_lattice.rank [number_field K] :
  finrank ℤ (unit_lattice K) = card (infinite_place K) - 1 :=
le_antisymm (unit_lattice.rank_le K) (unit_lattice.le_rank K)

end number_field.log_embedding
