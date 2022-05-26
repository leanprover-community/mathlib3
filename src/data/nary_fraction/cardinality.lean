import data.nary_fraction.basic
import set_theory.cardinal.continuum

/-!
-/

open cardinal
open_locale cardinal

namespace nary_fraction

variables {N : ℕ}

instance : has_card_continuum (nary_fraction $ N + 2) := pi.has_card_continuum _ _

@[simp] protected lemma card_quotient :
  #(quotient (@nary_fraction.setoid $ N + 2)) = #(nary_fraction $ N + 2) :=
mk_quotient_le.antisymm $ mk_le_of_injective injective_interleave_zero

instance : has_card_continuum (quotient (@nary_fraction.setoid $ N + 2)) :=
⟨by rw [nary_fraction.card_quotient, mk_eq_continuum]⟩

end nary_fraction

namespace cardinal

open nary_fraction

universe u

variables {α : Type u} [conditionally_complete_lattice α] [densely_ordered α]

section

variables {a b : α}

lemma continuum_le_mk_Icc (h : a < b) : 𝔠 ≤ #(Icc a b) :=
begin
  set c : Π I : nontrivial_interval α, I.Ioo :=
    λ I, classical.indefinite_description _ I.nonempty_Ioo,
  set f : quotient binary_fraction.setoid → Icc a b :=
    λ x, ⟨x.out.decode c ⟨a, b, h⟩, x.out.decode_mem_Icc _ _ 0⟩,
  have hf : strict_mono f := strict_mono_decode_out c _,
  simpa using lift_mk_le'.2 ⟨⟨f, hf.injective⟩⟩,
end

lemma continuum_le_mk_Ioo (h : a < b) : 𝔠 ≤ #(Ioo a b) :=
begin
  rcases exists_between h with ⟨a₁, ha, hlt⟩, rcases exists_between hlt with ⟨b₁, hab, hb⟩,
  calc 𝔠 ≤ #(Icc a₁ b₁) : continuum_le_mk_Icc hab
  ... ≤ #(Ioo a b) : mk_le_mk_of_subset (Icc_subset_Ioo ha hb)
end

lemma continuum_le_mk_Ico (h : a < b) : 𝔠 ≤ #(Ico a b) :=
(continuum_le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ico_self)

lemma continuum_le_mk_Ioc (h : a < b) : 𝔠 ≤ #(Ioc a b) :=
(continuum_le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ioc_self)

lemma continuum_le_mk_Ioi' (h : (Ioi a).nonempty) : 𝔠 ≤ #(Ioi a) :=
exists.elim h $ λ b hb, (continuum_le_mk_Ioo hb).trans $ mk_le_mk_of_subset Ioo_subset_Ioi_self

lemma continuum_le_mk_Ioi [no_top_order α] (a : α) : 𝔠 ≤ #(Ioi a) :=
continuum_le_mk_Ioi' (no_top a)

lemma continuum_le_mk_Ici' (h : (Ioi a).nonempty) : 𝔠 ≤ #(Ici a) :=
(continuum_le_mk_Ioi' h).trans $ mk_le_mk_of_subset Ioi_subset_Ici_self

lemma continuum_le_mk_Ici [no_top_order α] (a : α) : 𝔠 ≤ #(Ici a) :=
continuum_le_mk_Ici' (no_top a)

lemma continuum_le_mk_Iio' (h : (Iio a).nonempty) : 𝔠 ≤ #(Iio a) :=
@continuum_le_mk_Ioi' (order_dual α) _ _ a h

lemma continuum_le_mk_Iio [no_bot_order α] (a : α) : 𝔠 ≤ #(Iio a) :=
@continuum_le_mk_Ioi (order_dual α) _ _ _ a

lemma continuum_le_mk_Iic' (h : (Iio a).nonempty) : 𝔠 ≤ #(Iic a) :=
@continuum_le_mk_Ici' (order_dual α) _ _ a h

lemma continuum_le_mk_Iic [no_bot_order α] (a : α) : 𝔠 ≤ #(Iic a) :=
@continuum_le_mk_Ici (order_dual α) _ _ _ a

variable (α)

lemma continuum_le_mk [nontrivial α] : 𝔠 ≤ #α :=
let ⟨a, b, h⟩ := exists_lt_of_inf α in (continuum_le_mk_Icc h).trans $ mk_set_le _

end

variables [has_card_continuum α] {a b : α}

@[simp] lemma mk_Icc_eq_continuum (h : a < b) : #(Icc a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Icc h)

@[simp] lemma mk_Ico_eq_continuum (h : a < b) : #(Ico a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ico h)

@[simp] lemma mk_Ioc_eq_continuum (h : a < b) : #(Ioc a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioc h)

@[simp] lemma mk_Ioo_eq_continuum (h : a < b) : #(Ioo a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioo h)

lemma mk_Ici_eq_continuum' (h : (Ioi a).nonempty) : #(Ici a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ici' h)

@[simp] lemma mk_Ici_eq_continuum [no_top_order α] (a : α) : #(Ici a) = 𝔠 :=
mk_Ici_eq_continuum' (no_top a)

lemma mk_Ioi_eq_continuum' (h : (Ioi a).nonempty) : #(Ioi a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioi' h)

@[simp] lemma mk_Ioi_eq_continuum [no_top_order α] (a : α) : #(Ioi a) = 𝔠 :=
mk_Ioi_eq_continuum' (no_top a)

lemma mk_Iic_eq_continuum' (h : (Iio a).nonempty) : #(Iic a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Iic' h)

@[simp] lemma mk_Iic_eq_continuum [no_bot_order α] (a : α) : #(Iic a) = 𝔠 :=
mk_Iic_eq_continuum' (no_bot a)

lemma mk_Iio_eq_continuum' (h : (Iio a).nonempty) : #(Iio a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Iio' h)

@[simp] lemma mk_Iio_eq_continuum [no_bot_order α] (a : α) : #(Iio a) = 𝔠 :=
mk_Iio_eq_continuum' (no_bot a)

end cardinal
