import data.real.ennreal
import data.nat.enat

/-!
-/

open_locale classical nnreal ennreal
noncomputable theory

namespace enat

variables {m n : ℕ∞}

instance has_coe_ennreal : has_coe_t ℕ∞ ℝ≥0∞ := ⟨with_top.map coe⟩

@[simp] lemma map_coe_nnreal : @eq (ℕ∞ → ℝ≥0∞) (with_top.map (coe : ℕ → ℝ≥0)) coe := rfl

@[simps { fully_applied := ff }] def to_ennreal_order_embedding : ℕ∞ ↪o ℝ≥0∞ :=
nat.cast_order_embedding.with_top_map

@[simps { fully_applied := ff }] def to_ennreal_ring_hom : ℕ∞ →+* ℝ≥0∞ :=
(nat.cast_ring_hom ℝ≥0).with_top_map nat.cast_injective

@[simp, norm_cast] lemma coe_ennreal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ := rfl
@[simp, norm_cast] lemma coe_ennreal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n := rfl

@[simp, norm_cast] lemma coe_ennreal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
to_ennreal_order_embedding.le_iff_le

@[simp, norm_cast] lemma coe_ennreal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
to_ennreal_order_embedding.lt_iff_lt

@[mono] lemma coe_ennreal_mono : monotone (coe : ℕ∞ → ℝ≥0∞) := to_ennreal_order_embedding.monotone

@[mono] lemma coe_ennreal_strict_mono : strict_mono (coe : ℕ∞ → ℝ≥0∞) :=
to_ennreal_order_embedding.strict_mono

@[simp, norm_cast] lemma coe_ennreal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 := map_zero to_ennreal_ring_hom

@[simp] lemma coe_ennreal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
map_add to_ennreal_ring_hom m n

@[simp] lemma coe_ennreal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 := map_one to_ennreal_ring_hom

@[simp] lemma coe_ennreal_bit0 (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) := coe_ennreal_add n n

@[simp] lemma coe_ennreal_bit1 (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
map_bit1 to_ennreal_ring_hom n

end enat
