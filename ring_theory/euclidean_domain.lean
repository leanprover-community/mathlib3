import algebra.euclidean_domain ring_theory.ideals data.polynomial
noncomputable theory
local attribute [instance] classical.dec
open euclidean_domain set

def is_coprime {α} [ring α] (x y : α) : Prop :=
span ({x, y} : set α) = univ

theorem mem_span_pair {α} [ring α] {x y z : α} :
  z ∈ span (insert y {x} : set α) ↔ ∃ a b, a * x + b * y = z :=
begin
  simp [is_coprime, eq_univ_iff_forall, mem_span_insert, span_singleton],
  split; rintro ⟨b, a, e⟩,
  { exact ⟨a, -b, by simp [e]⟩ },
  { exact ⟨-a, b, by simp [e.symm]⟩ }
end

theorem is_coprime_def {α} [ring α] (x y : α) :
  is_coprime x y ↔ ∀ z, ∃ a b, a * x + b * y = z :=
by simp [is_coprime, eq_univ_iff_forall, mem_span_pair]

theorem is_coprime_self {α} [comm_ring α] (x y : α) :
  is_coprime x x ↔ is_unit x :=
by rw [← span_singleton_eq_univ]; simp [is_coprime]

theorem span_gcd {α} [euclidean_domain α] (x y : α) :
  span ({gcd x y} : set α) = span ({x, y} : set α) :=
begin
  apply subset.antisymm; refine span_minimal (by apply_instance) _,
  { simp [mem_span_pair],
    exact ⟨gcd_a x y, gcd_b x y, by simp [gcd_eq_gcd_ab x y, mul_comm]⟩ },
  { simp [mem_span_singleton_iff_dvd, gcd_dvd] }
end

theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} :
  is_unit (gcd x y) ↔ is_coprime x y :=
by rw [← span_singleton_eq_univ, span_gcd, is_coprime]

theorem is_coprime_of_dvd {α} [euclidean_domain α] {x y : α}
  (z : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  rw [← gcd_is_unit_iff],
  by_contra h,
  refine H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _),
  rwa [ne, gcd_eq_zero_iff]
end

theorem dvd_or_coprime {α} [euclidean_domain α] (x y : α)
  (h : is_irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
  refine or_iff_not_imp_left.2 (λ h', _),
  apply is_coprime_of_dvd,
  { rintro ⟨rfl, rfl⟩, simpa using h },
  { rintro z nu nz ⟨w, rfl⟩ dy,
    refine h' (dvd.trans _ dy),
    simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1 $
      (of_is_irreducible_mul h).resolve_left nu) }
end

theorem is_maximal_ideal_of_irreducible {α} [euclidean_domain α] {x : α}
  (irr : is_irreducible x) : is_maximal_ideal (span ({x} : set α)) :=
{ ne_univ := by simp [span_singleton_eq_univ]; exact irr.1,
  eq_or_univ_of_subset := λ S hS ss, begin
    refine or_iff_not_imp_left.2 (λ h, _),
    have : ¬ S ⊆ span {x}, {exact mt (subset.antisymm ss) (ne.symm h)},
    simp [subset_def, not_forall, mem_span_singleton_iff_dvd] at this,
    rcases this with ⟨y, h₁, h₂⟩,
    apply univ_subset_iff.1,
    simp [((dvd_or_coprime _ _ irr).resolve_left h₂).symm],
    apply span_minimal hS.to_is_submodule,
    simp [h₁, ss (subset_span (mem_singleton _))]
  end }

section
universe u
variables {K : Type u} [field K] (f : polynomial K) (irr : is_irreducible f)
include irr

def adjoin_root : Type u :=
@quotient_ring.quotient _ _
  (@span _ _ _ ring.to_module ({f} : set (polynomial K))) (is_ideal.span _)

instance adjoin_root.field : field (adjoin_root f irr) :=
begin
  haveI := is_maximal_ideal_of_irreducible irr,
  apply quotient_ring.field
end

variables {f irr}
def mk : polynomial K → adjoin_root f irr :=
@quotient_ring.mk _ _
  (@span _ _ _ ring.to_module ({f} : set (polynomial K))) (is_ideal.span _)

def root : adjoin_root f irr := mk polynomial.X

def inj (x : K) : adjoin_root f irr := mk (polynomial.C x)

instance adjoin_root.has_coe_t : has_coe_t K (adjoin_root f irr) := ⟨inj⟩

end
