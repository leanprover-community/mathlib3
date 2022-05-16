import data.real.ennreal

/-!
-/

open_locale classical nnreal ennreal
noncomputable theory

namespace enat

def to_ennreal : enat ↪o ℝ≥0∞ :=
enat.with_top_order_iso.to_order_embedding.trans $
  nat.cast_order_embedding.with_top

@[simp] lemma to_ennreal_top : to_ennreal ⊤ = ⊤ :=
by simp [to_ennreal]

@[simp] lemma to_ennreal_coe (n : ℕ) : to_ennreal (n : enat) = n :=
by simp [to_ennreal, with_top_order_iso]

def to_ennreal_add_monoid_hom : enat →+ ℝ≥0∞ :=
(nat.cast_add_monoid_hom ℝ≥0).with_top.comp with_top_add_equiv.to_add_monoid_hom

@[simp] lemma coe_to_ennreal_add_monoid_hom :
  ⇑to_ennreal_add_monoid_hom = to_ennreal := rfl

@[simp] lemma to_ennreal_zero : to_ennreal 0 = 0 :=
map_zero to_ennreal_add_monoid_hom

@[simp] lemma to_ennreal_add (m n : enat) : to_ennreal (m + n) = to_ennreal m + to_ennreal n :=
map_add to_ennreal_add_monoid_hom m n

@[simp] lemma to_ennreal_one : to_ennreal 1 = 1 :=
by simpa only [nat.cast_one] using to_ennreal_coe 1

@[simp] lemma to_ennreal_bit0 (n : enat) : to_ennreal (bit0 n) = bit0 (to_ennreal n) :=
to_ennreal_add n n

@[simp] lemma to_ennreal_bit1 (n : enat) : to_ennreal (bit1 n) = bit1 (to_ennreal n) :=
by simp only [bit1, to_ennreal_add, to_ennreal_bit0, to_ennreal_one]

end enat
