/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import algebra.divisibility.basic
import algebra.group_power.lemmas
import algebra.parity

/-!
# Associated, prime, and irreducible elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section prime
variables [comm_monoid_with_zero α]

/-- prime element of a `comm_monoid_with_zero` -/
def prime (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ (∀a b, p ∣ a * b → p ∣ a ∨ p ∣ b)

namespace prime
variables {p : α} (hp : prime p)
include hp

lemma ne_zero : p ≠ 0 :=
hp.1

lemma not_unit : ¬ is_unit p :=
hp.2.1

lemma not_dvd_one : ¬ p ∣ 1 :=
mt (is_unit_of_dvd_one _) hp.not_unit

lemma ne_one : p ≠ 1 :=
λ h, hp.2.1 (h.symm ▸ is_unit_one)

lemma dvd_or_dvd (hp : prime p) {a b : α} (h : p ∣ a * b) :
  p ∣ a ∨ p ∣ b :=
hp.2.2 a b h

lemma dvd_of_dvd_pow (hp : prime p) {a : α} {n : ℕ} (h : p ∣ a^n) :
  p ∣ a :=
begin
  induction n with n ih,
  { rw pow_zero at h,
    have := is_unit_of_dvd_one _ h,
    have := not_unit hp,
    contradiction },
  rw pow_succ at h,
  cases dvd_or_dvd hp h with dvd_a dvd_pow,
  { assumption },
  exact ih dvd_pow
end

end prime

@[simp] lemma not_prime_zero : ¬ prime (0 : α) :=
λ h, h.ne_zero rfl

@[simp] lemma not_prime_one : ¬ prime (1 : α) :=
λ h, h.not_unit is_unit_one

section map
variables [comm_monoid_with_zero β] {F : Type*} {G : Type*}
  [monoid_with_zero_hom_class F α β] [mul_hom_class G β α] (f : F) (g : G) {p : α}

lemma comap_prime (hinv : ∀ a, g (f a : β) = a) (hp : prime (f p)) : prime p :=
⟨ λ h, hp.1 $ by simp [h],  λ h, hp.2.1 $ h.map f,  λ a b h, by
  { refine (hp.2.2 (f a) (f b) $ by { convert map_dvd f h, simp }).imp _ _;
    { intro h, convert ← map_dvd g h; apply hinv } } ⟩

lemma mul_equiv.prime_iff (e : α ≃* β) : prime p ↔ prime (e p) :=
⟨ λ h, comap_prime e.symm e (λ a, by simp) $ (e.symm_apply_apply p).substr h,
  comap_prime e e.symm (λ a, by simp) ⟩

end map

end prime

lemma prime.left_dvd_or_dvd_right_of_dvd_mul [cancel_comm_monoid_with_zero α] {p : α}
  (hp : prime p) {a b : α} : a ∣ p * b → p ∣ a ∨ a ∣ b :=
begin
  rintro ⟨c, hc⟩,
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with h | ⟨x, rfl⟩,
  { exact or.inl h },
  { rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc,
    exact or.inr (hc.symm ▸ dvd_mul_right _ _) }
end

lemma prime.pow_dvd_of_dvd_mul_left
  [cancel_comm_monoid_with_zero α]
  {p a b : α} (hp : prime p) (n : ℕ) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b :=
begin
  induction n with n ih,
  { rw pow_zero, exact one_dvd b },
  { obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h'),
    rw pow_succ',
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h),
    rwa [←mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ←pow_succ', mul_left_comm] }
end

lemma prime.pow_dvd_of_dvd_mul_right
  [cancel_comm_monoid_with_zero α]
  {p a b : α} (hp : prime p) (n : ℕ) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a :=
by { rw [mul_comm] at h', exact hp.pow_dvd_of_dvd_mul_left n h h' }

lemma prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd [cancel_comm_monoid_with_zero α]
  {p a b : α} {n : ℕ} (hp : prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n)
  (hb : ¬ p ^ 2 ∣ b) : p ∣ a :=
begin
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  cases (hp.dvd_or_dvd ((dvd_pow_self p (nat.succ_ne_zero n)).trans hpow)) with H hbdiv,
  { exact hp.dvd_of_dvd_pow H },
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv,
  obtain ⟨y, hy⟩ := hpow,
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y,
  { refine mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) _,
    rw [← mul_assoc _ p, ← pow_succ', ← hy, mul_pow, ← mul_assoc (a ^ n.succ),
      mul_comm _ (p ^ n), mul_assoc] },
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right (λ hdvdx, hb _)),
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx,
  rw [pow_two, ← mul_assoc],
  exact dvd_mul_right _ _,
end

lemma prime_pow_succ_dvd_mul {α : Type*} [cancel_comm_monoid_with_zero α]
  {p x y : α} (h : prime p) {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) :
  p ^ (i + 1) ∣ x ∨ p ∣ y :=
begin
  rw or_iff_not_imp_right,
  intro hy,
  induction i with i ih generalizing x,
  { simp only [zero_add, pow_one] at *,
    exact (h.dvd_or_dvd hxy).resolve_right hy },
  rw pow_succ at hxy ⊢,
  obtain ⟨x', rfl⟩ := (h.dvd_or_dvd (dvd_of_mul_right_dvd hxy)).resolve_right hy,
  rw mul_assoc at hxy,
  exact mul_dvd_mul_left p (ih ((mul_dvd_mul_iff_left h.ne_zero).mp hxy)),
end

/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
structure irreducible [monoid α] (p : α) : Prop :=
(not_unit : ¬ is_unit p)
(is_unit_or_is_unit' : ∀a b, p = a * b → is_unit a ∨ is_unit b)

namespace irreducible

lemma not_dvd_one [comm_monoid α] {p : α} (hp : irreducible p) : ¬ p ∣ 1 :=
mt (is_unit_of_dvd_one _) hp.not_unit

lemma is_unit_or_is_unit [monoid α] {p : α} (hp : irreducible p) {a b : α} (h : p = a * b) :
  is_unit a ∨ is_unit b :=
hp.is_unit_or_is_unit' a b h

end irreducible

lemma irreducible_iff [monoid α] {p : α} :
  irreducible p ↔ ¬ is_unit p ∧ ∀a b, p = a * b → is_unit a ∨ is_unit b :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

@[simp] theorem not_irreducible_one [monoid α] : ¬ irreducible (1 : α) :=
by simp [irreducible_iff]

theorem irreducible.ne_one [monoid α] : ∀ {p:α}, irreducible p → p ≠ 1
| _ hp rfl := not_irreducible_one hp

@[simp] theorem not_irreducible_zero [monoid_with_zero α] : ¬ irreducible (0 : α)
| ⟨hn0, h⟩ := have is_unit (0:α) ∨ is_unit (0:α), from h 0 0 ((mul_zero 0).symm),
  this.elim hn0 hn0

theorem irreducible.ne_zero [monoid_with_zero α] : ∀ {p:α}, irreducible p → p ≠ 0
| _ hp rfl := not_irreducible_zero hp

theorem of_irreducible_mul {α} [monoid α] {x y : α} :
  irreducible (x * y) → is_unit x ∨ is_unit y
| ⟨_, h⟩ := h _ _ rfl

theorem of_irreducible_pow {α} [monoid α] {x : α} {n : ℕ} (hn : n ≠ 1) :
  irreducible (x ^ n) → is_unit x :=
begin
  obtain hn|hn := hn.lt_or_lt,
  { simp only [nat.lt_one_iff.mp hn, is_empty.forall_iff, not_irreducible_one, pow_zero] },
  intro h,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hn,
  rw [pow_succ, add_comm] at h,
  exact (or_iff_left_of_imp is_unit_pow_succ_iff.mp).mp (of_irreducible_mul h)
end

theorem irreducible_or_factor {α} [monoid α] (x : α) (h : ¬ is_unit x) :
  irreducible x ∨ ∃ a b, ¬ is_unit a ∧ ¬ is_unit b ∧ a * b = x :=
begin
  haveI := classical.dec,
  refine or_iff_not_imp_right.2 (λ H, _),
  simp [h, irreducible_iff] at H ⊢,
  refine λ a b h, classical.by_contradiction $ λ o, _,
  simp [not_or_distrib] at o,
  exact H _ o.1 _ o.2 h.symm
end

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
lemma irreducible.dvd_symm [monoid α] {p q : α}
  (hp : irreducible p) (hq : irreducible q) : p ∣ q → q ∣ p :=
begin
  unfreezingI { rintros ⟨q', rfl⟩ },
  rw is_unit.mul_right_dvd (or.resolve_left (of_irreducible_mul hq) hp.not_unit),
end

lemma irreducible.dvd_comm [monoid α] {p q : α}
  (hp : irreducible p) (hq : irreducible q) : p ∣ q ↔ q ∣ p :=
⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section
variables [monoid α]

lemma irreducible_units_mul (a : αˣ) (b : α) : irreducible (↑a * b) ↔ irreducible b :=
begin
  simp only [irreducible_iff, units.is_unit_units_mul, and.congr_right_iff],
  refine λ hu, ⟨λ h A B HAB, _, λ h A B HAB, _⟩,
  { rw [←a.is_unit_units_mul],
    apply h,
    rw [mul_assoc, ←HAB] },
  { rw [←(a⁻¹).is_unit_units_mul],
    apply h,
    rw [mul_assoc, ←HAB, units.inv_mul_cancel_left] },
end

lemma irreducible_is_unit_mul {a b : α} (h : is_unit a) : irreducible (a * b) ↔ irreducible b :=
let ⟨a, ha⟩ := h in ha ▸ irreducible_units_mul a b

lemma irreducible_mul_units (a : αˣ) (b : α) : irreducible (b * ↑a) ↔ irreducible b :=
begin
  simp only [irreducible_iff, units.is_unit_mul_units, and.congr_right_iff],
  refine λ hu, ⟨λ h A B HAB, _, λ h A B HAB, _⟩,
  { rw [←units.is_unit_mul_units B a],
    apply h,
    rw [←mul_assoc, ←HAB] },
  { rw [←units.is_unit_mul_units B a⁻¹],
    apply h,
    rw [←mul_assoc, ←HAB, units.mul_inv_cancel_right] },
end

lemma irreducible_mul_is_unit {a b : α} (h : is_unit a) : irreducible (b * a) ↔ irreducible b :=
let ⟨a, ha⟩ := h in ha ▸ irreducible_mul_units a b

lemma irreducible_mul_iff {a b : α} :
  irreducible (a * b) ↔ (irreducible a ∧ is_unit b) ∨ (irreducible b ∧ is_unit a) :=
begin
  split,
  { refine λ h, or.imp (λ h', ⟨_, h'⟩) (λ h', ⟨_, h'⟩) (h.is_unit_or_is_unit rfl).symm,
    { rwa [irreducible_mul_is_unit h'] at h },
    { rwa [irreducible_is_unit_mul h'] at h } },
  { rintros (⟨ha, hb⟩|⟨hb, ha⟩),
    { rwa [irreducible_mul_is_unit hb] },
    { rwa [irreducible_is_unit_mul ha] } },
end

end

section comm_monoid
variables [comm_monoid α] {a : α}

lemma irreducible.not_square (ha : irreducible a) : ¬ is_square a :=
by { rintro ⟨b, rfl⟩, simp only [irreducible_mul_iff, or_self] at ha, exact ha.1.not_unit ha.2 }

lemma is_square.not_irreducible (ha : is_square a) : ¬ irreducible a := λ h, h.not_square ha

end comm_monoid

section cancel_comm_monoid_with_zero
variables [cancel_comm_monoid_with_zero α] {a p : α}

protected lemma prime.irreducible (hp : prime p) : irreducible p :=
⟨hp.not_unit, λ a b hab,
  (show a * b ∣ a ∨ a * b ∣ b, from hab ▸ hp.dvd_or_dvd (hab ▸ dvd_rfl)).elim
    (λ ⟨x, hx⟩, or.inr (is_unit_iff_dvd_one.2
      ⟨x, mul_right_cancel₀ (show a ≠ 0, from λ h, by simp [*, prime] at *)
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))
    (λ ⟨x, hx⟩, or.inl (is_unit_iff_dvd_one.2
      ⟨x, mul_right_cancel₀ (show b ≠ 0, from λ h, by simp [*, prime] at *)
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))⟩

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : prime p) {a b : α} {k l : ℕ} :
  p ^ k ∣ a → p ^ l ∣ b → p ^ ((k + l) + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩,
have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z),
  by simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz,
have hp0: p ^ (k + l) ≠ 0, from pow_ne_zero _ hp.ne_zero,
have hpd : p ∣ x * y, from ⟨z, by rwa [mul_right_inj' hp0] at h⟩,
(hp.dvd_or_dvd hpd).elim
  (λ ⟨d, hd⟩, or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
  (λ ⟨d, hd⟩, or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)

lemma prime.not_square (hp : prime p) : ¬ is_square p := hp.irreducible.not_square
lemma is_square.not_prime (ha : is_square a) : ¬ prime a := λ h, h.not_square ha

lemma pow_not_prime {n : ℕ} (hn : n ≠ 1) : ¬ prime (a ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ of_irreducible_pow hn $ hp.irreducible

end cancel_comm_monoid_with_zero

/-- Two elements of a `monoid` are `associated` if one of them is another one
multiplied by a unit on the right. -/
def associated [monoid α] (x y : α) : Prop := ∃u:αˣ, x * u = y

local infix ` ~ᵤ ` : 50 := associated

namespace associated

@[refl] protected theorem refl [monoid α] (x : α) : x ~ᵤ x := ⟨1, by simp⟩
instance [monoid α] : is_refl α associated := ⟨associated.refl⟩

@[symm] protected theorem symm [monoid α] : ∀{x y : α}, x ~ᵤ y → y ~ᵤ x
| x _ ⟨u, rfl⟩ := ⟨u⁻¹, by rw [mul_assoc, units.mul_inv, mul_one]⟩
instance [monoid α] : is_symm α associated := ⟨λ a b, associated.symm⟩

protected theorem comm [monoid α] {x y : α} : x ~ᵤ y ↔ y ~ᵤ x :=
⟨associated.symm, associated.symm⟩

@[trans] protected theorem trans [monoid α] : ∀{x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
| x _ _ ⟨u, rfl⟩ ⟨v, rfl⟩ := ⟨u * v, by rw [units.coe_mul, mul_assoc]⟩
instance [monoid α] : is_trans α associated := ⟨λ a b c, associated.trans⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (α : Type*) [monoid α] : setoid α :=
{ r := associated, iseqv := ⟨associated.refl, λa b, associated.symm, λa b c, associated.trans⟩ }

end associated

local attribute [instance] associated.setoid

theorem unit_associated_one [monoid α] {u : αˣ} : (u : α) ~ᵤ 1 := ⟨u⁻¹, units.mul_inv u⟩

theorem associated_one_iff_is_unit [monoid α] {a : α} : (a : α) ~ᵤ 1 ↔ is_unit a :=
iff.intro
  (assume h, let ⟨c, h⟩ := h.symm in h ▸ ⟨c, (one_mul _).symm⟩)
  (assume ⟨c, h⟩, associated.symm ⟨c, by simp [h]⟩)

theorem associated_zero_iff_eq_zero [monoid_with_zero α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
iff.intro
  (assume h, let ⟨u, h⟩ := h.symm in by simpa using h.symm)
  (assume h, h ▸ associated.refl a)

theorem associated_one_of_mul_eq_one [comm_monoid α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
show (units.mk_of_mul_eq_one a b hab : α) ~ᵤ 1, from unit_associated_one

theorem associated_one_of_associated_mul_one [comm_monoid α] {a b : α} :
  a * b ~ᵤ 1 → a ~ᵤ 1
| ⟨u, h⟩ := associated_one_of_mul_eq_one (b * u) $ by simpa [mul_assoc] using h

lemma associated_mul_unit_left {β : Type*} [monoid β] (a u : β) (hu : is_unit u) :
  associated (a * u) a :=
let ⟨u', hu⟩ := hu in ⟨u'⁻¹, hu ▸ units.mul_inv_cancel_right _ _⟩

lemma associated_unit_mul_left {β : Type*} [comm_monoid β] (a u : β) (hu : is_unit u) :
  associated (u * a) a :=
begin
  rw mul_comm,
  exact associated_mul_unit_left _ _ hu
end

lemma associated_mul_unit_right {β : Type*} [monoid β] (a u : β) (hu : is_unit u) :
  associated a (a * u) :=
(associated_mul_unit_left a u hu).symm

lemma associated_unit_mul_right {β : Type*} [comm_monoid β] (a u : β) (hu : is_unit u) :
  associated a (u * a) :=
(associated_unit_mul_left a u hu).symm

lemma associated_mul_is_unit_left_iff {β : Type*} [monoid β] {a u b : β} (hu : is_unit u) :
  associated (a * u) b ↔ associated a b :=
⟨trans (associated_mul_unit_right _ _ hu), trans (associated_mul_unit_left _ _ hu)⟩

lemma associated_is_unit_mul_left_iff {β : Type*} [comm_monoid β] {u a b : β} (hu : is_unit u) :
  associated (u * a) b ↔ associated a b :=
begin
  rw mul_comm,
  exact associated_mul_is_unit_left_iff hu
end

lemma associated_mul_is_unit_right_iff {β : Type*} [monoid β] {a b u : β} (hu : is_unit u) :
  associated a (b * u) ↔ associated a b :=
associated.comm.trans $ (associated_mul_is_unit_left_iff hu).trans associated.comm

lemma associated_is_unit_mul_right_iff {β : Type*} [comm_monoid β] {a u b : β} (hu : is_unit u) :
  associated a (u * b) ↔ associated a b :=
associated.comm.trans $ (associated_is_unit_mul_left_iff hu).trans associated.comm

@[simp]
lemma associated_mul_unit_left_iff {β : Type*} [monoid β] {a b : β} {u : units β} :
  associated (a * u) b ↔ associated a b :=
associated_mul_is_unit_left_iff u.is_unit

@[simp]
lemma associated_unit_mul_left_iff {β : Type*} [comm_monoid β] {a b : β} {u : units β} :
  associated (↑u * a) b ↔ associated a b :=
associated_is_unit_mul_left_iff u.is_unit

@[simp]
lemma associated_mul_unit_right_iff {β : Type*} [monoid β] {a b : β} {u : units β} :
  associated a (b * u) ↔ associated a b :=
associated_mul_is_unit_right_iff u.is_unit

@[simp]
lemma associated_unit_mul_right_iff {β : Type*} [comm_monoid β] {a b : β} {u : units β} :
  associated a (↑u * b) ↔ associated a b :=
associated_is_unit_mul_right_iff u.is_unit

lemma associated.mul_mul [comm_monoid α] {a₁ a₂ b₁ b₂ : α} :
  a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → (a₁ * a₂) ~ᵤ (b₁ * b₂)
| ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ := ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩

lemma associated.mul_left [comm_monoid α] (a : α) {b c : α} (h : b ~ᵤ c) :
  (a * b) ~ᵤ (a * c) :=
(associated.refl a).mul_mul h

lemma associated.mul_right [comm_monoid α] {a b : α} (h : a ~ᵤ b) (c : α) :
  (a * c) ~ᵤ (b * c) :=
h.mul_mul (associated.refl c)

lemma associated.pow_pow [comm_monoid α] {a b : α} {n : ℕ} (h : a ~ᵤ b) :
  a ^ n ~ᵤ b ^ n :=
begin
  induction n with n ih, { simp [h] },
  convert h.mul_mul ih;
    rw pow_succ
end

protected lemma associated.dvd [monoid α] {a b : α} : a ~ᵤ b → a ∣ b := λ ⟨u, hu⟩, ⟨u, hu.symm⟩

protected lemma associated.dvd_dvd [monoid α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
⟨h.dvd, h.symm.dvd⟩

theorem associated_of_dvd_dvd [cancel_monoid_with_zero α]
  {a b : α} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b :=
begin
  rcases hab with ⟨c, rfl⟩,
  rcases hba with ⟨d, a_eq⟩,
  by_cases ha0 : a = 0,
  { simp [*] at * },
  have hac0 : a * c ≠ 0,
  { intro con, rw [con, zero_mul] at a_eq, apply ha0 a_eq, },
  have : a * (c * d) =  a * 1 := by rw [← mul_assoc, ← a_eq, mul_one],
  have hcd : (c * d) = 1, from mul_left_cancel₀ ha0 this,
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one],
  have hdc : d * c = 1, from mul_left_cancel₀ hac0 this,
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩
end

theorem dvd_dvd_iff_associated [cancel_monoid_with_zero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
⟨λ ⟨h1, h2⟩, associated_of_dvd_dvd h1 h2, associated.dvd_dvd⟩

instance [cancel_monoid_with_zero α] [decidable_rel ((∣) : α → α → Prop)] :
  decidable_rel ((~ᵤ) : α → α → Prop) :=
λ a b, decidable_of_iff _ dvd_dvd_iff_associated

lemma associated.dvd_iff_dvd_left [monoid α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ units.mul_right_dvd.symm

lemma associated.dvd_iff_dvd_right [monoid α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ units.dvd_mul_right.symm

lemma associated.eq_zero_iff [monoid_with_zero α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
⟨λ ha, let ⟨u, hu⟩ := h in by simp [hu.symm, ha],
  λ hb, let ⟨u, hu⟩ := h.symm in by simp [hu.symm, hb]⟩

lemma associated.ne_zero_iff [monoid_with_zero α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
not_congr h.eq_zero_iff

protected lemma associated.prime [comm_monoid_with_zero α] {p q : α} (h : p ~ᵤ q) (hp : prime p) :
  prime q :=
⟨h.ne_zero_iff.1 hp.ne_zero,
  let ⟨u, hu⟩ := h in
    ⟨λ ⟨v, hv⟩, hp.not_unit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩,
      hu ▸ by { simp [units.mul_right_dvd], intros a b, exact hp.dvd_or_dvd }⟩⟩

lemma irreducible.associated_of_dvd [cancel_monoid_with_zero α] {p q : α}
  (p_irr : irreducible p) (q_irr : irreducible q) (dvd : p ∣ q) : associated p q :=
associated_of_dvd_dvd dvd (p_irr.dvd_symm q_irr dvd)

lemma irreducible.dvd_irreducible_iff_associated [cancel_monoid_with_zero α]
  {p q : α} (pp : irreducible p) (qp : irreducible q) :
  p ∣ q ↔ associated p q :=
⟨irreducible.associated_of_dvd pp qp, associated.dvd⟩

lemma prime.associated_of_dvd [cancel_comm_monoid_with_zero α] {p q : α}
  (p_prime : prime p) (q_prime : prime q) (dvd : p ∣ q) : associated p q :=
p_prime.irreducible.associated_of_dvd q_prime.irreducible dvd

theorem prime.dvd_prime_iff_associated [cancel_comm_monoid_with_zero α]
  {p q : α} (pp : prime p) (qp : prime q) :
  p ∣ q ↔ associated p q :=
pp.irreducible.dvd_irreducible_iff_associated qp.irreducible
lemma associated.prime_iff [comm_monoid_with_zero α] {p q : α}
  (h : p ~ᵤ q) : prime p ↔ prime q :=
⟨h.prime, h.symm.prime⟩

protected lemma associated.is_unit [monoid α] {a b : α} (h :  a ~ᵤ b) : is_unit a → is_unit b :=
let ⟨u, hu⟩ := h in λ ⟨v, hv⟩, ⟨v * u, by simp [hv, hu.symm]⟩

lemma associated.is_unit_iff [monoid α] {a b : α} (h :  a ~ᵤ b) : is_unit a ↔ is_unit b :=
⟨h.is_unit, h.symm.is_unit⟩

protected lemma associated.irreducible [monoid α] {p q : α} (h : p ~ᵤ q)
  (hp : irreducible p) : irreducible q :=
⟨mt h.symm.is_unit hp.1,
  let ⟨u, hu⟩ := h in λ a b hab,
  have hpab : p = a * (b * (u⁻¹ : αˣ)),
    from calc p = (p * u) * (u ⁻¹ : αˣ) : by simp
      ... = _ : by rw hu; simp [hab, mul_assoc],
  (hp.is_unit_or_is_unit hpab).elim or.inl (λ ⟨v, hv⟩, or.inr ⟨v * u, by simp [hv]⟩)⟩

protected lemma associated.irreducible_iff [monoid α] {p q : α} (h : p ~ᵤ q) :
  irreducible p ↔ irreducible q :=
⟨h.irreducible, h.symm.irreducible⟩

lemma associated.of_mul_left [cancel_comm_monoid_with_zero α] {a b c d : α}
  (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d :=
let ⟨u, hu⟩ := h in let ⟨v, hv⟩ := associated.symm h₁ in
⟨u * (v : αˣ), mul_left_cancel₀ ha
  begin
    rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu],
    simp [hv.symm, mul_assoc, mul_comm, mul_left_comm]
  end⟩

lemma associated.of_mul_right [cancel_comm_monoid_with_zero α] {a b c d : α} :
  a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c :=
by rw [mul_comm a, mul_comm c]; exact associated.of_mul_left

lemma associated.of_pow_associated_of_prime [cancel_comm_monoid_with_zero α] {p₁ p₂ : α}
  {k₁ k₂ : ℕ} (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) :
  p₁ ~ᵤ p₂ :=
begin
  have : p₁ ∣ p₂ ^ k₂,
  { rw ←h.dvd_iff_dvd_right,
    apply dvd_pow_self _ hk₁.ne' },
  rw ←hp₁.dvd_prime_iff_associated hp₂,
  exact hp₁.dvd_of_dvd_pow this,
end

lemma associated.of_pow_associated_of_prime' [cancel_comm_monoid_with_zero α] {p₁ p₂ : α}
  {k₁ k₂ : ℕ} (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) :
  p₁ ~ᵤ p₂ :=
(h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

section unique_units
variables [monoid α] [unique αˣ]

lemma units_eq_one (u : αˣ) : u = 1 := subsingleton.elim u 1

theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y :=
begin
  split,
  { rintro ⟨c, rfl⟩, rw [units_eq_one c, units.coe_one, mul_one] },
  { rintro rfl, refl },
end

theorem associated_eq_eq : (associated : α → α → Prop) = eq :=
by { ext, rw associated_iff_eq }

lemma prime_dvd_prime_iff_eq
  {M : Type*} [cancel_comm_monoid_with_zero M] [unique Mˣ] {p q : M} (pp : prime p) (qp : prime q) :
  p ∣ q ↔ p = q :=
by rw [pp.dvd_prime_iff_associated qp, ←associated_eq_eq]

end unique_units

section unique_units₀

variables {R : Type*} [cancel_comm_monoid_with_zero R] [unique Rˣ] {p₁ p₂ : R} {k₁ k₂ : ℕ}

lemma eq_of_prime_pow_eq (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) :
  p₁ = p₂ :=
by { rw [←associated_iff_eq] at h ⊢, apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁ }

lemma eq_of_prime_pow_eq' (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₁ : 0 < k₂) (h : p₁ ^ k₁ = p₂ ^ k₂) :
  p₁ = p₂ :=
by { rw [←associated_iff_eq] at h ⊢, apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁ }

end unique_units₀

/-- The quotient of a monoid by the `associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `associates α`. -/
def associates (α : Type*) [monoid α] : Type* :=
quotient (associated.setoid α)

namespace associates
open associated

/-- The canonical quotient map from a monoid `α` into the `associates` of `α` -/
protected def mk {α : Type*} [monoid α] (a : α) : associates α :=
⟦ a ⟧

instance [monoid α] : inhabited (associates α) := ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_associated [monoid α] {a b : α} :
  associates.mk a = associates.mk b ↔ a ~ᵤ b :=
iff.intro quotient.exact quot.sound

theorem quotient_mk_eq_mk [monoid α] (a : α) : ⟦ a ⟧ = associates.mk a := rfl

theorem quot_mk_eq_mk [monoid α] (a : α) : quot.mk setoid.r a = associates.mk a := rfl

theorem forall_associated [monoid α] {p : associates α → Prop} :
  (∀a, p a) ↔ (∀a, p (associates.mk a)) :=
iff.intro
  (assume h a, h _)
  (assume h a, quotient.induction_on a h)

theorem mk_surjective [monoid α] : function.surjective (@associates.mk α _) :=
forall_associated.2 (λ a, ⟨a, rfl⟩)

instance [monoid α] : has_one (associates α) := ⟨⟦ 1 ⟧⟩

@[simp] lemma mk_one [monoid α] : associates.mk (1 : α) = 1 := rfl

theorem one_eq_mk_one [monoid α] : (1 : associates α) = associates.mk 1 := rfl

instance [monoid α] : has_bot (associates α) := ⟨1⟩

lemma bot_eq_one [monoid α] : (⊥ : associates α) = 1 := rfl

lemma exists_rep [monoid α] (a : associates α) : ∃ a0 : α, associates.mk a0 = a :=
quot.exists_rep a

instance [monoid α] [subsingleton α] : unique (associates α) :=
{ default := 1,
  uniq := λ a, by { apply quotient.rec_on_subsingleton₂, intros a b, congr } }

lemma mk_injective [monoid α] [unique (units α)] : function.injective (@associates.mk α _) :=
λ a b h, associated_iff_eq.mp (associates.mk_eq_mk_iff_associated.mp h)

section comm_monoid
variable [comm_monoid α]

instance : has_mul (associates α) :=
⟨λa' b', quotient.lift_on₂ a' b' (λa b, ⟦ a * b ⟧) $
  assume a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩,
  quotient.sound $ ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩⟩

theorem mk_mul_mk {x y : α} : associates.mk x * associates.mk y = associates.mk (x * y) :=
rfl

instance : comm_monoid (associates α) :=
{ one       := 1,
  mul       := (*),
  mul_one   := assume a', quotient.induction_on a' $
    assume a, show ⟦a * 1⟧ = ⟦ a ⟧, by simp,
  one_mul   := assume a', quotient.induction_on a' $
    assume a, show ⟦1 * a⟧ = ⟦ a ⟧, by simp,
  mul_assoc := assume a' b' c', quotient.induction_on₃ a' b' c' $
    assume a b c, show ⟦a * b * c⟧ = ⟦a * (b * c)⟧, by rw [mul_assoc],
  mul_comm  := assume a' b', quotient.induction_on₂ a' b' $
    assume a b, show ⟦a * b⟧ = ⟦b * a⟧, by rw [mul_comm] }

instance : preorder (associates α) :=
{ le := has_dvd.dvd,
  le_refl := dvd_refl,
  le_trans := λ a b c, dvd_trans}

/-- `associates.mk` as a `monoid_hom`. -/
protected def mk_monoid_hom : α →* (associates α) := ⟨associates.mk, mk_one, λ x y, mk_mul_mk⟩

@[simp] lemma mk_monoid_hom_apply (a : α) : associates.mk_monoid_hom a = associates.mk a := rfl

lemma associated_map_mk {f : associates α →* α}
  (hinv : function.right_inverse f associates.mk) (a : α) :
  a ~ᵤ f (associates.mk a) :=
associates.mk_eq_mk_iff_associated.1 (hinv (associates.mk a)).symm

lemma mk_pow (a : α) (n : ℕ) : associates.mk (a ^ n) = (associates.mk a) ^ n :=
by induction n; simp [*, pow_succ, associates.mk_mul_mk.symm]

lemma dvd_eq_le : ((∣) : associates α → associates α → Prop) = (≤) := rfl

theorem mul_eq_one_iff {x y : associates α} : x * y = 1 ↔ (x = 1 ∧ y = 1) :=
iff.intro
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b ~ᵤ 1, from quotient.exact h,
    ⟨quotient.sound $ associated_one_of_associated_mul_one this,
      quotient.sound $ associated_one_of_associated_mul_one $ by rwa [mul_comm] at this⟩)
  (by simp {contextual := tt})

theorem units_eq_one (u : (associates α)ˣ) : u = 1 :=
units.ext (mul_eq_one_iff.1 u.val_inv).1

instance unique_units : unique ((associates α)ˣ) :=
{ default := 1, uniq := associates.units_eq_one }

theorem coe_unit_eq_one (u : (associates α)ˣ): (u : associates α) = 1 :=
by simp

theorem is_unit_iff_eq_one (a : associates α) : is_unit a ↔ a = 1 :=
iff.intro
  (assume ⟨u, h⟩, h ▸ coe_unit_eq_one _)
  (assume h, h.symm ▸ is_unit_one)

lemma is_unit_iff_eq_bot {a : associates α} : is_unit a ↔ a = ⊥ :=
by rw [associates.is_unit_iff_eq_one, bot_eq_one]

theorem is_unit_mk {a : α} : is_unit (associates.mk a) ↔ is_unit a :=
calc is_unit (associates.mk a) ↔ a ~ᵤ 1 :
    by rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
  ... ↔ is_unit a : associated_one_iff_is_unit

section order

theorem mul_mono {a b c d : associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
  a * c ≤ b * d :=
let ⟨x, hx⟩ := h₁, ⟨y, hy⟩ := h₂ in
⟨x * y, by simp [hx, hy, mul_comm, mul_assoc, mul_left_comm]⟩

theorem one_le {a : associates α} : 1 ≤ a :=
dvd.intro _ (one_mul a)

theorem le_mul_right {a b : associates α} : a ≤ a * b := ⟨b, rfl⟩

theorem le_mul_left {a b : associates α} : a ≤ b * a :=
by rw [mul_comm]; exact le_mul_right

instance : order_bot (associates α) :=
{ bot := 1,
  bot_le := assume a, one_le }

end order

theorem dvd_of_mk_le_mk {a b : α} : associates.mk a ≤ associates.mk b → a ∣ b
| ⟨c', hc'⟩ := (quotient.induction_on c' $ assume c hc,
    let ⟨d, hd⟩ := (quotient.exact hc).symm in
    ⟨(↑d) * c,
      calc b = (a * c) * ↑d : hd.symm
        ... = a * (↑d * c) : by ac_refl⟩) hc'

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → associates.mk a ≤ associates.mk b :=
assume ⟨c, hc⟩, ⟨associates.mk c, by simp [hc]; refl⟩

theorem mk_le_mk_iff_dvd_iff {a b : α} : associates.mk a ≤ associates.mk b ↔ a ∣ b :=
iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

theorem mk_dvd_mk {a b : α} : associates.mk a ∣ associates.mk b ↔ a ∣ b :=
iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

end comm_monoid

instance [has_zero α] [monoid α] : has_zero (associates α) := ⟨⟦ 0 ⟧⟩
instance [has_zero α] [monoid α] : has_top (associates α) := ⟨0⟩

section monoid_with_zero
variables [monoid_with_zero α]

@[simp] theorem mk_eq_zero {a : α} : associates.mk a = 0 ↔ a = 0 :=
⟨assume h, (associated_zero_iff_eq_zero a).1 $ quotient.exact h, assume h, h.symm ▸ rfl⟩

theorem mk_ne_zero {a : α} : associates.mk a ≠ 0 ↔ a ≠ 0 :=
not_congr mk_eq_zero

instance [nontrivial α] : nontrivial (associates α) :=
⟨⟨0, 1,
assume h,
have (0 : α) ~ᵤ 1, from quotient.exact h,
have (0 : α) = 1, from ((associated_zero_iff_eq_zero 1).1 this.symm).symm,
zero_ne_one this⟩⟩

lemma exists_non_zero_rep {a : associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ associates.mk a0 = a :=
quotient.induction_on a (λ b nz, ⟨b, mt (congr_arg quotient.mk) nz, rfl⟩)

end monoid_with_zero

section comm_monoid_with_zero

variables [comm_monoid_with_zero α]

instance : comm_monoid_with_zero (associates α) :=
{ zero_mul := by { rintro ⟨a⟩, show associates.mk (0 * a) = associates.mk 0, rw [zero_mul] },
  mul_zero := by { rintro ⟨a⟩, show associates.mk (a * 0) = associates.mk 0, rw [mul_zero] },
  .. associates.comm_monoid, .. associates.has_zero }

instance : order_top (associates α) :=
{ top := 0,
  le_top := assume a, ⟨0, (mul_zero a).symm⟩ }

instance : bounded_order (associates α) :=
{ .. associates.order_top,
  .. associates.order_bot }

instance [decidable_rel ((∣) : α → α → Prop)] :
  decidable_rel ((∣) : associates α → associates α → Prop) :=
λ a b, quotient.rec_on_subsingleton₂ a b (λ a b, decidable_of_iff' _ mk_dvd_mk)

lemma prime.le_or_le {p : associates α} (hp : prime p) {a b : associates α} (h : p ≤ a * b) :
  p ≤ a ∨ p ≤ b :=
hp.2.2 a b h

lemma prime_mk (p : α) : prime (associates.mk p) ↔ _root_.prime p :=
begin
  rw [prime, _root_.prime, forall_associated],
  transitivity,
  { apply and_congr, refl,
    apply and_congr, refl,
    apply forall_congr, assume a,
    exact forall_associated },
  apply and_congr mk_ne_zero,
  apply and_congr,
  { rw [is_unit_mk], },
  refine forall₂_congr (λ a b, _),
  rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk],
end

theorem irreducible_mk (a : α) : irreducible (associates.mk a) ↔ irreducible a :=
begin
  simp only [irreducible_iff, is_unit_mk],
  apply and_congr iff.rfl,
  split,
  { rintro h x y rfl,
    simpa [is_unit_mk] using h (associates.mk x) (associates.mk y) rfl },
  { intros h x y,
    refine quotient.induction_on₂ x y (assume x y a_eq, _),
    rcases quotient.exact a_eq.symm with ⟨u, a_eq⟩,
    rw mul_assoc at a_eq,
    show is_unit (associates.mk x) ∨ is_unit (associates.mk y),
    simpa [is_unit_mk] using h _ _ a_eq.symm }
end

theorem mk_dvd_not_unit_mk_iff {a b : α} :
  dvd_not_unit (associates.mk a) (associates.mk b) ↔
  dvd_not_unit a b :=
begin
  rw [dvd_not_unit, dvd_not_unit, mk_ne_zero],
  apply and_congr_right, intro ane0,
  split,
  { contrapose!, rw forall_associated,
    intros h x hx hbax,
    rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax,
    cases hbax with u hu,
    apply h (x * ↑u⁻¹),
    { rw is_unit_mk at hx,
      rw associated.is_unit_iff,
      apply hx,
      use u,
      simp, },
    simp [← mul_assoc, ← hu] },
  { rintro ⟨x, ⟨hx, rfl⟩⟩,
    use associates.mk x,
    simp [is_unit_mk, mk_mul_mk, hx], }
end

theorem dvd_not_unit_of_lt {a b : associates α} (hlt : a < b) :
  dvd_not_unit a b :=
begin
  split, { rintro rfl, apply not_lt_of_le _ hlt, apply dvd_zero },
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩,
  refine ⟨x, _, rfl⟩,
  contrapose! ndvd,
  rcases ndvd with ⟨u, rfl⟩,
  simp,
end

theorem irreducible_iff_prime_iff :
  (∀ a : α, irreducible a ↔ prime a) ↔ (∀ a : (associates α), irreducible a ↔ prime a) :=
by simp_rw [forall_associated, irreducible_mk, prime_mk]

end comm_monoid_with_zero

section cancel_comm_monoid_with_zero
variable [cancel_comm_monoid_with_zero α]

instance : partial_order (associates α) :=
{ le_antisymm := λ a' b', quotient.induction_on₂ a' b' (λ a b hab hba,
  quot.sound $ associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba))
  .. associates.preorder }

instance : ordered_comm_monoid (associates α) :=
{ mul_le_mul_left := λ a b ⟨d, hd⟩ c, hd.symm ▸ mul_assoc c a d ▸ le_mul_right,
  ..associates.comm_monoid,
  ..associates.partial_order}

instance : no_zero_divisors (associates α) :=
⟨λ x y,
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b = 0, from (associated_zero_iff_eq_zero _).1 (quotient.exact h),
    have a = 0 ∨ b = 0, from mul_eq_zero.1 this,
    this.imp (assume h, h.symm ▸ rfl) (assume h, h.symm ▸ rfl))⟩

instance : cancel_comm_monoid_with_zero (associates α) :=
{ mul_left_cancel_of_ne_zero :=
    begin
      rintros ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h,
      rcases quotient.exact' h with ⟨u, hu⟩,
      rw [mul_assoc] at hu,
      exact quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩
    end,
  .. (infer_instance : comm_monoid_with_zero (associates α)) }

lemma le_of_mul_le_mul_left (a b c : associates α) (ha : a ≠ 0) :
  a * b ≤ a * c → b ≤ c
| ⟨d, hd⟩ := ⟨d, mul_left_cancel₀ ha $ by rwa ← mul_assoc⟩

lemma one_or_eq_of_le_of_prime :
  ∀(p m : associates α), prime p → m ≤ p → (m = 1 ∨ m = p)
| _ m ⟨hp0, hp1, h⟩ ⟨d, rfl⟩ :=
match h m d dvd_rfl with
| or.inl h := classical.by_cases (assume : m = 0, by simp [this]) $
  assume : m ≠ 0,
  have m * d ≤ m * 1, by simpa using h,
  have d ≤ 1, from associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this,
  have d = 1, from bot_unique this,
  by simp [this]
| or.inr h := classical.by_cases (assume : d = 0, by simp [this] at hp0; contradiction) $
  assume : d ≠ 0,
  have d * m ≤ d * 1, by simpa [mul_comm] using h,
  or.inl $ bot_unique $ associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
end

instance : canonically_ordered_monoid (associates α) :=
{ exists_mul_of_le := λ a b, id,
  le_self_mul := λ a b, ⟨b, rfl⟩,
  ..associates.cancel_comm_monoid_with_zero,
  ..associates.bounded_order,
  ..associates.ordered_comm_monoid}

theorem dvd_not_unit_iff_lt {a b : associates α} :
  dvd_not_unit a b ↔ a < b :=
dvd_and_not_dvd_iff.symm

lemma le_one_iff {p : associates α} : p ≤ 1 ↔ p = 1 :=
by rw [← associates.bot_eq_one, le_bot_iff]

end cancel_comm_monoid_with_zero

end associates

section comm_monoid_with_zero

lemma dvd_not_unit.is_unit_of_irreducible_right [comm_monoid_with_zero α] {p q : α}
  (h : dvd_not_unit p q) (hq : irreducible q) : is_unit p :=
begin
  obtain ⟨hp', x, hx, hx'⟩ := h,
  exact or.resolve_right ((irreducible_iff.1 hq).right p x hx') hx
end

lemma not_irreducible_of_not_unit_dvd_not_unit [comm_monoid_with_zero α] {p q : α}
  (hp : ¬is_unit p) (h : dvd_not_unit p q) : ¬ irreducible q :=
mt h.is_unit_of_irreducible_right hp

lemma dvd_not_unit.not_unit [comm_monoid_with_zero α] {p q : α}
  (hp : dvd_not_unit p q) : ¬ is_unit q :=
begin
  obtain ⟨-, x, hx, rfl⟩ := hp,
  exact λ hc, hx (is_unit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (is_unit_iff_dvd_one.mp hc))),
end

lemma dvd_not_unit_of_dvd_not_unit_associated [comm_monoid_with_zero α]
  [nontrivial α] {p q r : α} (h : dvd_not_unit p q) (h' : associated q r) : dvd_not_unit p r :=
begin
  obtain ⟨u, rfl⟩ := associated.symm h',
  obtain ⟨hp, x, hx⟩ := h,
  refine ⟨hp, x * ↑(u⁻¹), dvd_not_unit.not_unit ⟨u⁻¹.ne_zero, x, hx.left, mul_comm _ _⟩, _⟩,
  rw [← mul_assoc, ← hx.right, mul_assoc, units.mul_inv, mul_one]
end

end comm_monoid_with_zero

section cancel_comm_monoid_with_zero

lemma is_unit_of_associated_mul [cancel_comm_monoid_with_zero α]
  {p b : α} (h : associated (p * b) p) (hp : p ≠ 0) : is_unit b :=
begin
  cases h with a ha,
  refine is_unit_of_mul_eq_one b a ((mul_right_inj' hp).mp _),
  rwa [← mul_assoc, mul_one],
end

lemma dvd_not_unit.not_associated [cancel_comm_monoid_with_zero α] {p q : α}
  (h : dvd_not_unit p q) : ¬ associated p q :=
begin
  rintro ⟨a, rfl⟩,
  obtain ⟨hp, x, hx, hx'⟩ := h,
  rcases (mul_right_inj' hp).mp hx' with rfl,
  exact hx a.is_unit,
end

lemma dvd_not_unit.ne [cancel_comm_monoid_with_zero α] {p q : α}
  (h : dvd_not_unit p q) : p ≠ q :=
begin
  by_contra hcontra,
  obtain ⟨hp, x, hx', hx''⟩ := h,
  conv_lhs at hx'' {rw [← hcontra, ← mul_one p]},
  rw (mul_left_cancel₀ hp hx'').symm at hx',
  exact hx' is_unit_one,
end

lemma pow_injective_of_not_unit [cancel_comm_monoid_with_zero α] {q : α}
  (hq : ¬ is_unit q) (hq' : q ≠ 0): function.injective (λ (n : ℕ), q^n) :=
begin
  refine injective_of_lt_imp_ne (λ n m h, dvd_not_unit.ne ⟨pow_ne_zero n hq', q^(m - n), _, _⟩),
  { exact not_is_unit_of_not_is_unit_dvd hq (dvd_pow (dvd_refl _) (nat.sub_pos_of_lt h).ne') },
  { exact (pow_mul_pow_sub q h.le).symm  }
end

lemma dvd_prime_pow [cancel_comm_monoid_with_zero α] {p q : α} (hp : prime p) (n : ℕ) :
  q ∣ p^n ↔ ∃ i ≤ n, associated q (p ^ i) :=
begin
  induction n with n ih generalizing q,
  { simp [← is_unit_iff_dvd_one, associated_one_iff_is_unit] },
  refine ⟨λ h, _, λ ⟨i, hi, hq⟩, hq.dvd.trans (pow_dvd_pow p hi)⟩,
  rw pow_succ at h,
  rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno),
  { rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h,
    rcases h with ⟨i, hi, hq⟩,
    refine ⟨i + 1, nat.succ_le_succ hi, (hq.mul_left p).trans _⟩,
    rw pow_succ },
  { obtain ⟨i, hi, hq⟩ := ih.mp hno,
    exact ⟨i, hi.trans n.le_succ, hq⟩ }
end

end cancel_comm_monoid_with_zero

assert_not_exists multiset
