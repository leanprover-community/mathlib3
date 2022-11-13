import data.enat.card
import set_theory.cardinal.basic

/-!
-/

universes u v
open function set
open_locale cardinal classical

namespace cardinal

instance has_coe_enat : has_coe_t ℕ∞ cardinal := ⟨option.elim ℵ₀ coe⟩

@[simp] lemma enat_cast_top : ((⊤ : ℕ∞) : cardinal) = ℵ₀ := rfl
@[simp, norm_cast] lemma coe_coe (n : ℕ) : ((n : ℕ∞) : cardinal) = n := rfl
@[simp, norm_cast] lemma enat_cast_zero : ((0 : ℕ∞) : cardinal) = 0 := rfl

@[simp, norm_cast] lemma enat_cast_one : ((1 : ℕ∞) : cardinal) = 1 :=
by rw [← nat.cast_one, coe_coe, nat.cast_one]

lemma enat_le_aleph_0 (n : ℕ∞) : ↑n ≤ ℵ₀ :=
by { cases n, exacts [le_rfl, (nat_lt_aleph_0 _).le] }

@[simp] lemma range_enat_cast : range (coe : ℕ∞ → cardinal) = Iic ℵ₀ :=
by simp only [with_top.range_eq, (∘), coe_coe, enat_cast_top, range_nat_cast, Iio_insert]

lemma le_aleph_0' {c} : c ≤ ℵ₀ ↔ ∃ n : ℕ∞, ↑n = c :=
set.ext_iff.1 range_enat_cast.symm c

lemma le_aleph_0 {c} : c ≤ ℵ₀ ↔ ∃ n : ℕ∞, c = n :=
le_aleph_0'.trans $ exists_congr $ λ _, eq_comm

lemma eq_enat_or_aleph_0_lt (c : cardinal) : (∃ n : ℕ∞, c = n) ∨ ℵ₀ < c :=
(le_or_lt _ _).imp_left le_aleph_0.1

@[simp] lemma aleph_0_add_enat (n : ℕ∞) : ℵ₀ + n = ℵ₀ :=
by { cases n, exacts [aleph_0_add_aleph_0, aleph_0_add_nat _] }

@[simp] lemma enat_add_aleph_0 (n : ℕ∞) : ↑n + ℵ₀ = ℵ₀ :=
by rw [add_comm, aleph_0_add_enat]

@[simp] lemma aleph_0_mul_enat {n : ℕ∞} (hn : n ≠ 0) : ℵ₀ * n = ℵ₀ :=
by { cases n, exacts [aleph_0_mul_aleph_0, aleph_0_mul_nat (mt with_top.coe_eq_zero.2 hn)] }

@[simp] lemma enat_mul_aleph_0 {n : ℕ∞} (hn : n ≠ 0) : ↑n * ℵ₀ = ℵ₀ :=
by rw [mul_comm, aleph_0_mul_enat hn]

instance can_lift_enat : can_lift cardinal ℕ∞ coe (≤ ℵ₀) :=
⟨λ c h, (le_aleph_0.1 h).imp $ λ _, eq.symm⟩

@[mono] lemma enat_cast_strict_mono : strict_mono (coe : ℕ∞ → cardinal) :=
with_top.strict_mono_iff.2 ⟨λ m n, nat_cast_lt.2, nat_lt_aleph_0⟩

@[mono] lemma enat_cast_mono : monotone (coe : ℕ∞ → cardinal) := enat_cast_strict_mono.monotone

def enat_cast_order_embedding : ℕ∞ ↪o cardinal :=
order_embedding.of_strict_mono coe enat_cast_strict_mono

@[simp, norm_cast] lemma enat_cast_le {m n : ℕ∞} : (m : cardinal) ≤ n ↔ m ≤ n :=
enat_cast_strict_mono.le_iff_le

@[simp, norm_cast] lemma enat_cast_lt {m n : ℕ∞} : (m : cardinal) < n ↔ m < n :=
enat_cast_strict_mono.lt_iff_lt

lemma enat_cast_injective : injective (coe : ℕ∞ → cardinal) :=
enat_cast_strict_mono.injective

@[simp, norm_cast] lemma enat_cast_inj {m n : ℕ∞} : (m : cardinal) = n ↔ m = n :=
enat_cast_injective.eq_iff

@[simp] lemma enat_cast_eq_zero {m : ℕ∞} : (m : cardinal) = 0 ↔ m = 0 :=
enat_cast_zero ▸ enat_cast_inj

@[simp] lemma enat_cast_pos {m : ℕ∞} : 0 < (m : cardinal) ↔ 0 < m := enat_cast_zero ▸ enat_cast_lt

@[simp] lemma lift_enat_cast : ∀ m : ℕ∞, lift.{u v} m = m
| ⊤ := by simp
| (m : ℕ) := by simp

@[simp] lemma enat_cast_eq_lift {m : ℕ∞} {c : cardinal.{v}} : ↑m = lift.{u} c ↔ ↑m = c :=
by rw [← lift_enat_cast, lift_inj]

@[simp] lemma lift_eq_enat_cast {m : ℕ∞} {c : cardinal.{v}} : lift.{u} c = m ↔ c = m :=
by rw [← lift_enat_cast, lift_inj]

lemma to_enat_aux_infinite (α : Type*) [infinite α] :
  extend (coe : ℕ∞ → cardinal) id (const _ ⊤) (#α) = ⊤ :=
begin
  cases (aleph_0_le_mk α).eq_or_lt with hα hα,
  { rw [← hα, ← enat_cast_top, extend_apply enat_cast_injective, id] },
  { rw [extend_apply'], rwa [← le_aleph_0', not_le] }
end

lemma to_enat_aux (α : Type*) : extend (coe : ℕ∞ → cardinal) id (const _ ⊤) (#α) = #ₑα :=
begin
  casesI fintype_or_infinite α,
  { rw [mk_fintype, ← coe_coe, extend_apply enat_cast_injective, id, enat.card_fintype] },
  { rw [to_enat_aux_infinite, enat.card_infinite] }
end

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
to `⊤`. -/
noncomputable def to_enat : cardinal →+* ℕ∞ :=
{ to_fun := extend (coe : ℕ∞ → cardinal) id (const _ ⊤),
  map_one' := by rw [← mk_punit, to_enat_aux, enat.card_punit],
  map_mul' := λ x y, induction_on₂ x y $ λ α β, by simp only [mul_def, to_enat_aux, enat.card_prod],
  map_zero' := by rw [← mk_pempty, to_enat_aux, enat.card_empty],
  map_add' := λ x y, induction_on₂ x y $ λ α β, by simp only [add_def, to_enat_aux, enat.card_sum] }

@[simp, norm_cast] lemma to_enat_enat (n : ℕ∞) : to_enat n = n :=
extend_apply enat_cast_injective _ _ _

@[simp, norm_cast] lemma to_enat_nat (n : ℕ∞) : to_enat n = n := to_enat_enat n
@[simp, norm_cast] lemma to_enat_mk (α : Type*) : to_enat #α = #ₑ α := to_enat_aux α

@[simp] lemma to_enat_of_aleph_0_le {c : cardinal} (hc : ℵ₀ ≤ c) : to_enat c = ⊤ :=
induction_on c (λ α hα, @to_enat_aux_infinite α (infinite_iff.2 hα)) hc

@[simp] lemma le_to_enat {n : ℕ∞} {c : cardinal} : n ≤ to_enat c ↔ ↑n ≤ c :=
begin
  cases le_total c ℵ₀ with hc hc,
  { rcases le_aleph_0.1 hc with ⟨m, rfl⟩,
    rw [enat_cast_le, to_enat_enat] },
  { simp only [to_enat_of_aleph_0_le hc, le_top, (enat_le_aleph_0 _).trans hc] }
end

lemma gc_to_enat : galois_connection coe to_enat := λ n c, le_to_enat.symm

/-- Coercion `ℕ∞ → cardinal` and `cardinal.to_enat` form a Galois coinsertion. -/
noncomputable def gi_to_enat : galois_coinsertion coe to_enat :=
gc_to_enat.to_galois_coinsertion $ λ n, (to_enat_enat _).le

lemma to_enat_surjective : surjective to_enat := gi_to_enat.u_surjective
@[simp] lemma range_to_enat : range to_enat = univ := to_enat_surjective.range_eq
@[simp] lemma to_enat_eq_top {c : cardinal} : to_enat c = ⊤ ↔  ℵ₀ ≤ c := gc_to_enat.u_eq_top

@[simp] lemma to_enat_eq_nat {c : cardinal} {n : ℕ} : to_enat c = n ↔ c = n :=
induction_on c $ λ α, by simp only [to_enat_mk, mk_eq_nat_iff, enat.card_eq_nat_iff]

@[simp] lemma to_enat_eq_zero {c : cardinal} : to_enat c = 0 ↔ c = 0 := to_enat_eq_nat

@[simp] lemma to_enat_eq_one {c : cardinal} : to_enat c = 1 ↔ c = 1 :=
by rw [← enat.coe_one, to_enat_eq_nat, nat.cast_one]

@[simp] lemma to_enat_lift (c : cardinal.{v}) : (lift.{u} c).to_enat = c.to_enat :=
induction_on c $ λ α, by rw [← mk_ulift, to_enat_mk, to_enat_mk, enat.card_ulift]

lemma enat_cast_eq_iff {n : ℕ∞} {c : cardinal} : ↑n = c ↔ c.to_enat = n ∧ c ≤ ℵ₀ :=
⟨λ h, h ▸ ⟨to_enat_enat _, enat_le_aleph_0 _⟩,
  λ h, by { lift c to ℕ∞ using h.2, simpa only [to_enat_enat, enat_cast_inj] using h.1.symm }⟩

/-- Coercion `ℕ∞ → cardinal` is a ring homomorphism. -/
instance enat_coe_is_ring_hom : coe_is_ring_hom ℕ∞ cardinal :=
{ coe_one := enat_cast_eq_iff.2 ⟨map_one _, one_le_aleph_0⟩,
  coe_mul := λ m n, enat_cast_eq_iff.2 ⟨by rw [map_mul, to_enat_enat, to_enat_enat],
    aleph_0_mul_aleph_0 ▸ mul_le_mul' (enat_le_aleph_0 _) (enat_le_aleph_0 _)⟩,
  coe_zero := rfl,
  coe_add := λ m n, enat_cast_eq_iff.2 ⟨by rw [map_add, to_enat_enat, to_enat_enat],
    add_le_aleph_0.2 ⟨enat_le_aleph_0 _, enat_le_aleph_0 _⟩⟩ }

@[simp] lemma cast_to_enat_eq_self {c : cardinal} : ↑c.to_enat = c ↔ c ≤ ℵ₀ :=
⟨λ h, h ▸ enat_le_aleph_0 _, λ h, by { lift c to ℕ∞ using h, rw [to_enat_enat] }⟩

alias cast_to_enat_eq_self ↔ _ cast_to_enat_of_le_aleph_0

lemma cast_to_enat_le_self (c : cardinal) : ↑c.to_enat ≤ c := gc_to_enat.l_u_le _

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
to 0. -/
noncomputable def to_nat : cardinal →*₀ ℕ := enat.to_nat.comp to_enat.to_monoid_with_zero_hom

@[simp] lemma to_nat_to_enat (c : cardinal) : c.to_enat.to_nat = c.to_nat := rfl
@[simp] lemma to_nat_enat (n : ℕ∞) : to_nat n = n.to_nat := by rw [← to_nat_to_enat, to_enat_enat]
@[simp] lemma to_nat_nat (n : ℕ) : to_nat n = n := by rw [← coe_coe, to_nat_enat, enat.to_nat_coe]

@[simp] lemma to_nat_mk (α : Type*) : (#α).to_nat = #ₙ α :=
by rw [← to_nat_to_enat, to_enat_mk, enat.to_nat_card]

lemma to_nat_apply_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : c.to_nat = 0 :=
by rw [← to_nat_to_enat, to_enat_of_aleph_0_le h, enat.to_nat_top]

lemma cast_to_nat_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) : ↑c.to_nat = c :=
by { lift c to ℕ using h, rw [to_nat_nat] }

lemma cast_to_nat_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : ↑c.to_nat = (0 : cardinal) :=
by rw [to_nat_apply_of_aleph_0_le h, nat.cast_zero]

lemma to_nat_le_iff_le_of_lt_aleph_0 {c d : cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
  c.to_nat ≤ d.to_nat ↔ c ≤ d :=
by rw [←nat_cast_le, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

lemma to_nat_lt_iff_lt_of_lt_aleph_0 {c d : cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
  c.to_nat < d.to_nat ↔ c < d :=
by rw [←nat_cast_lt, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

lemma to_nat_le_of_le_of_lt_aleph_0 {c d : cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) :
  c.to_nat ≤ d.to_nat :=
(to_nat_le_iff_le_of_lt_aleph_0 (hcd.trans_lt hd) hd).mpr hcd

lemma to_nat_lt_of_lt_of_lt_aleph_0 {c d : cardinal} (hd : d < ℵ₀) (hcd : c < d) :
  c.to_nat < d.to_nat :=
(to_nat_lt_iff_lt_of_lt_aleph_0 (hcd.trans hd) hd).mpr hcd

/-- `to_nat` has a right-inverse: coercion. -/
lemma to_nat_right_inverse : function.right_inverse (coe : ℕ → cardinal) to_nat := to_nat_nat

lemma to_nat_surjective : surjective to_nat := to_nat_right_inverse.surjective

@[simp] theorem aleph_0_to_nat : to_nat ℵ₀ = 0 := to_nat_apply_of_aleph_0_le le_rfl

lemma to_nat_eq_iff {c : cardinal} {n : ℕ} (hn : n ≠ 0) : to_nat c = n ↔ c = n :=
by rw [← to_nat_to_enat, enat.to_nat_eq_iff hn, to_enat_eq_nat]

@[simp] lemma to_nat_eq_one {c : cardinal} : to_nat c = 1 ↔ c = 1 :=
by rw [to_nat_eq_iff one_ne_zero, nat.cast_one]

lemma to_nat_eq_one_iff_unique {α : Type*} : (#α).to_nat = 1 ↔ subsingleton α ∧ nonempty α :=
to_nat_eq_one.trans eq_one_iff_unique

@[simp] lemma to_nat_lift (c : cardinal.{v}) : (lift.{u v} c).to_nat = c.to_nat :=
by rw [← to_nat_to_enat, to_enat_lift, to_nat_to_enat]

@[simp] lemma to_nat_add_of_lt_aleph_0 {a : cardinal.{u}} {b : cardinal.{v}}
  (ha : a < ℵ₀) (hb : b < ℵ₀) : ((lift.{v u} a) + (lift.{u v} b)).to_nat = a.to_nat + b.to_nat :=
begin
  lift a to ℕ using ha,
  lift b to ℕ using hb,
  rw [lift_nat_cast, lift_nat_cast, ← nat.cast_add, to_nat_nat, to_nat_nat, to_nat_nat]
end

end cardinal
