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

@[simp, norm_cast] lemma enat_cast_add : ∀ m n : ℕ∞, ↑(m + n) = (m + n : cardinal)
| ⊤ n := by rw [top_add, enat_cast_top, aleph_0_add_enat]
| m ⊤ := by rw [add_top, enat_cast_top, enat_add_aleph_0]
| (m : ℕ) (n : ℕ) := by rw [← with_top.coe_add, coe_coe, nat.cast_add, coe_coe, coe_coe]

@[simp, norm_cast] lemma enat_cast_mul (m n : ℕ∞) : ↑(m * n) = (m * n : cardinal) :=
begin
  rcases eq_or_ne m 0 with rfl|hm, { simp },
  rcases eq_or_ne n 0 with rfl|hn, { simp },
  induction m using with_top.rec_top_coe, { simp [hn] },
  rw [ne.def, with_top.coe_eq_zero] at hm,
  induction n using with_top.rec_top_coe, { simp [hm] },
  simp only [← nat.cast_mul, coe_coe]
end

/-- Coersion `coe : ℕ∞ → cardinal` as a ring homomorphism. -/
@[simps] def enat_cast_hom : ℕ∞ →+* cardinal :=
⟨coe, enat_cast_one, enat_cast_mul, enat_cast_zero, enat_cast_add⟩

@[simp, norm_cast] lemma enat_cast_bit0 (m : ℕ∞) : ↑(bit0 m) = (bit0 m : cardinal) :=
enat_cast_hom.map_bit0 _

@[simp, norm_cast] lemma enat_cast_bit1 (m : ℕ∞) : ↑(bit1 m) = (bit1 m : cardinal) :=
enat_cast_hom.map_bit1 _

@[simp, norm_cast] lemma enat_cast_pow (m : ℕ∞) (n : ℕ) : ↑(m ^ n) = (m ^ n : cardinal) :=
map_pow enat_cast_hom m n

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

noncomputable def to_enat_aux : cardinal → ℕ∞ := extend (coe : ℕ∞ → cardinal) id (const _ ⊤)

lemma to_enat_aux_enat (n : ℕ∞) : to_enat_aux n = n := extend_apply enat_cast_injective _ _ _
lemma to_enat_aux_nat (n : ℕ) : to_enat_aux n = n := to_enat_aux_enat n
lemma to_enat_aux_zero : to_enat_aux 0 = 0 := to_enat_aux_nat 0
lemma to_enat_aux_aleph_0 : to_enat_aux ℵ₀ = ⊤ := to_enat_aux_enat ⊤

lemma gc_to_enat_aux : galois_connection coe to_enat_aux :=
begin
  intros n c,
  cases le_or_lt c ℵ₀ with hc hc,
  { rcases le_aleph_0.1 hc with ⟨m, rfl⟩,
    rw [enat_cast_le, to_enat_aux_enat] },
  { rw [to_enat_aux, extend_apply'],
    { simp [(enat_le_aleph_0 _).trans hc.le] },
    { rintro ⟨_, rfl⟩, exact hc.not_le (enat_le_aleph_0 _) } }
end

lemma to_enat_aux_eq_top {c : cardinal} : to_enat_aux c = ⊤ ↔  ℵ₀ ≤ c := gc_to_enat_aux.u_eq_top

lemma to_enat_aux_eq_nat {c : cardinal} {n : ℕ} : to_enat_aux c = n ↔ c = n :=
begin
  cases lt_or_le c ℵ₀ with hc hc,
  { rcases lt_aleph_0.1 hc with ⟨m, rfl⟩, simp [to_enat_aux_nat] },
  { simp only [to_enat_aux_eq_top.2 hc, with_top.top_ne_coe, ((nat_lt_aleph_0 _).trans_le hc).ne'] }
end

lemma to_enat_aux_eq_zero {c : cardinal} : to_enat_aux c = 0 ↔ c = 0 := to_enat_aux_eq_nat

lemma to_enat_aux_lift (c : cardinal.{v}) : (lift.{u} c).to_enat_aux = c.to_enat_aux :=
begin
  cases le_total c ℵ₀ with hc hc,
  { lift c to ℕ∞ using hc, simp [to_enat_aux_enat] },
  { rw [to_enat_aux_eq_top.2 hc, to_enat_aux_eq_top.2 (aleph_0_le_lift.2 hc)] }
end

/-- An auxiliary definition, use `cardinal.gi_to_enat` instead. -/
noncomputable def gi_to_enat_aux : galois_coinsertion coe to_enat_aux :=
gc_to_enat_aux.to_galois_coinsertion $ λ n, (to_enat_aux_enat _).le

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
to `⊤`. -/
noncomputable def to_enat : cardinal →+* ℕ∞ :=
{ to_fun := to_enat_aux,
  map_one' := by rw [← nat.cast_one, to_enat_aux_nat, nat.cast_one],
  map_mul' := λ x y,
    begin
      rcases eq_or_ne x 0 with rfl|hx₀, { simp only [to_enat_aux_zero, zero_mul] },
      rcases eq_or_ne y 0 with rfl|hy₀, { simp only [to_enat_aux_zero, mul_zero] },
      cases lt_or_le x ℵ₀ with hx hx,
      { lift x to ℕ using hx,
        cases lt_or_le y ℵ₀ with hy hy,
        { lift y to ℕ using hy, simp only [to_enat_aux_nat, ← nat.cast_mul] },
        { rw [to_enat_aux_eq_top.2 (aleph_0_le_mul_iff.2 ⟨hx₀, hy₀, or.inr hy⟩), to_enat_aux_nat,
            to_enat_aux_eq_top.2 hy, with_top.mul_top],
          simpa using hx₀ } },
      { rw [to_enat_aux_eq_top.2 hx, with_top.top_mul (to_enat_aux_eq_zero.not.mpr hy₀),
          to_enat_aux_eq_top.2 (aleph_0_le_mul_iff.2 ⟨hx₀, hy₀, or.inl hx⟩)] }
    end,
  map_zero' := to_enat_aux_zero,
  map_add' := λ x y,
    begin
      cases le_or_lt ℵ₀ x with hx hx,
      { rw [to_enat_aux_eq_top.2 hx, top_add, to_enat_aux_eq_top.2 (le_add_right hx)] },
      { cases le_or_lt ℵ₀ y with hy hy,
        { rw [to_enat_aux_eq_top.2 hy, add_top, to_enat_aux_eq_top.2 (le_add_left hy)] },
        { lift x to ℕ using hx, lift y to ℕ using hy,
          simp only [← nat.cast_add, to_enat_aux_nat] } }
    end }

@[simp] lemma to_enat_enat (n : ℕ∞) : to_enat n = n := to_enat_aux_enat n
@[simp] lemma to_enat_nat (n : ℕ) : to_enat n = n := to_enat_enat n
@[simp] lemma to_enat_zero : to_enat 0 = 0 := to_enat_nat 0
@[simp] lemma to_enat_aleph_0 : to_enat ℵ₀ = ⊤ := to_enat_enat ⊤

lemma gc_to_enat : galois_connection coe to_enat := gc_to_enat_aux

@[simp] lemma le_to_enat {c : cardinal} {n : ℕ∞} : n ≤ c.to_enat ↔ ↑n ≤ c :=
gc_to_enat.le_iff_le.symm

@[simp] lemma to_enat_eq_top {c : cardinal} : to_enat c = ⊤ ↔ ℵ₀ ≤ c := to_enat_aux_eq_top
@[simp] lemma to_enat_eq_nat {c : cardinal} {n : ℕ} : to_enat c = n ↔ c = n := to_enat_aux_eq_nat
@[simp] lemma to_enat_eq_zero {c : cardinal} : to_enat c = 0 ↔ c = 0 := to_enat_eq_nat

@[simp] lemma to_enat_eq_one {c : cardinal} : to_enat c = 1 ↔ c = 1 :=
by rw [← enat.coe_one, to_enat_eq_nat, nat.cast_one]

alias to_enat_eq_top ↔ _ to_enat_of_aleph_0_le

@[simp] lemma cast_to_enat_eq_self {c : cardinal} : ↑c.to_enat = c ↔ c ≤ ℵ₀ :=
⟨λ h, h ▸ enat_le_aleph_0 _, λ h, by { lift c to ℕ∞ using h, rw [to_enat_enat] }⟩

alias cast_to_enat_eq_self ↔ _ cast_to_enat_of_le_aleph_0

lemma cast_to_enat_le_self (c : cardinal) : ↑c.to_enat ≤ c := gc_to_enat.l_u_le _

/-- Coercion `ℕ∞ → cardinal` and `cardinal.to_enat` form a Galois coinsertion. -/
noncomputable def gi_to_enat : galois_coinsertion coe to_enat := gi_to_enat_aux

lemma to_enat_surjective : surjective to_enat := gi_to_enat.u_surjective

@[simp] lemma range_to_enat : range to_enat = univ := to_enat_surjective.range_eq

@[simp] lemma to_enat_lift (c : cardinal.{v}) : (lift.{u} c).to_enat = c.to_enat :=
to_enat_aux_lift c

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
to 0. -/
noncomputable def to_nat : cardinal →*₀ ℕ := enat.to_nat.comp to_enat.to_monoid_with_zero_hom

@[simp] lemma to_nat_to_enat (c : cardinal) : c.to_enat.to_nat = c.to_nat := rfl
@[simp] lemma to_nat_enat (n : ℕ∞) : to_nat n = n.to_nat := by rw [← to_nat_to_enat, to_enat_enat]
@[simp] lemma to_nat_nat (n : ℕ) : to_nat n = n := by rw [← coe_coe, to_nat_enat, enat.to_nat_coe]

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
