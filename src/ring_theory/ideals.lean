/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import algebra.associated linear_algebra.basic order.zorn

universes u v
variables {α : Type u} {β : Type v} [comm_ring α] {a b : α}
open set function lattice

local attribute [instance] classical.prop_decidable

namespace ideal
variable (I : ideal α)

@[extensionality] lemma ext {I J : ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
submodule.ext h

theorem eq_top_of_unit_mem
  (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
eq_top_iff.2 $ λ z _, calc
    z = z * (y * x) : by simp [h]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ I : I.mul_mem_left hx

theorem eq_top_of_is_unit_mem {x} (hx : x ∈ I) (h : is_unit x) : I = ⊤ :=
let ⟨y, hy⟩ := is_unit_iff_exists_inv'.1 h in eq_top_of_unit_mem I x y hx hy

theorem eq_top_iff_one : I = ⊤ ↔ (1:α) ∈ I :=
⟨by rintro rfl; trivial,
 λ h, eq_top_of_unit_mem _ _ 1 h (by simp)⟩

theorem ne_top_iff_one : I ≠ ⊤ ↔ (1:α) ∉ I :=
not_congr I.eq_top_iff_one

def span (s : set α) : ideal α := submodule.span α s

lemma subset_span {s : set α} : s ⊆ span s := submodule.subset_span

lemma span_le {s : set α} {I} : span s ≤ I ↔ s ⊆ I := submodule.span_le

lemma span_mono {s t : set α} : s ⊆ t → span s ≤ span t := submodule.span_mono

@[simp] lemma span_eq : span (I : set α) = I := submodule.span_eq _

@[simp] lemma span_singleton_one : span ({1} : set α) = ⊤ :=
(eq_top_iff_one _).2 $ subset_span $ mem_singleton _

lemma mem_span_insert {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃ a (z ∈ span s), x = a * y + z := submodule.mem_span_insert

lemma mem_span_insert' {s : set α} {x y} :
  x ∈ span (insert y s) ↔ ∃a, x + a * y ∈ span s := submodule.mem_span_insert'

lemma mem_span_singleton' {x y : α} :
  x ∈ span ({y} : set α) ↔ ∃ a, a * y = x := submodule.mem_span_singleton

lemma mem_span_singleton {x y : α} :
  x ∈ span ({y} : set α) ↔ y ∣ x :=
mem_span_singleton'.trans $ exists_congr $ λ _, by rw [eq_comm, mul_comm]; refl

lemma span_singleton_le_span_singleton {x y : α} :
  span ({x} : set α) ≤ span ({y} : set α) ↔ y ∣ x :=
span_le.trans $ singleton_subset_iff.trans mem_span_singleton

lemma span_eq_bot {s : set α} : span s = ⊥ ↔ ∀ x ∈ s, (x:α) = 0 := submodule.span_eq_bot

lemma span_singleton_eq_bot {x} : span ({x} : set α) = ⊥ ↔ x = 0 := submodule.span_singleton_eq_bot

lemma span_singleton_eq_top {x} : span ({x} : set α) = ⊤ ↔ is_unit x :=
by rw [is_unit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one, eq_top_iff]

@[class] def is_prime (I : ideal α) : Prop :=
I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I

theorem is_prime.mem_or_mem {I : ideal α} (hI : I.is_prime) :
  ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I := hI.2

theorem is_prime.mem_or_mem_of_mul_eq_zero {I : ideal α} (hI : I.is_prime)
  {x y : α} (h : x * y = 0) : x ∈ I ∨ y ∈ I :=
hI.2 (h.symm ▸ I.zero_mem)

theorem is_prime.mem_of_pow_mem {I : ideal α} (hI : I.is_prime)
  {r : α} (n : ℕ) (H : r^n ∈ I) : r ∈ I :=
begin
  induction n with n ih,
  { exact (mt (eq_top_iff_one _).2 hI.1).elim H },
  exact or.cases_on (hI.mem_or_mem H) id ih
end

@[class] def zero_ne_one_of_proper {I : ideal α} (h : I ≠ ⊤) : (0:α) ≠ 1 :=
λ hz, I.ne_top_iff_one.1 h $ hz ▸ I.zero_mem

theorem span_singleton_prime {p : α} (hp : p ≠ 0) :
  is_prime (span ({p} : set α)) ↔ prime p :=
by simp [is_prime, prime, span_singleton_eq_top, hp, mem_span_singleton]

@[class] def is_maximal (I : ideal α) : Prop :=
I ≠ ⊤ ∧ ∀ J, I < J → J = ⊤

theorem is_maximal_iff {I : ideal α} : I.is_maximal ↔
  (1:α) ∉ I ∧ ∀ (J : ideal α) x, I ≤ J → x ∉ I → x ∈ J → (1:α) ∈ J :=
and_congr I.ne_top_iff_one $ forall_congr $ λ J,
by rw [lt_iff_le_not_le]; exact
 ⟨λ H x h hx₁ hx₂, J.eq_top_iff_one.1 $
    H ⟨h, not_subset.2 ⟨_, hx₂, hx₁⟩⟩,
  λ H ⟨h₁, h₂⟩, let ⟨x, xJ, xI⟩ := not_subset.1 h₂ in
   J.eq_top_iff_one.2 $ H x h₁ xI xJ⟩

theorem is_maximal.eq_of_le {I J : ideal α}
  (hI : I.is_maximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
eq_iff_le_not_lt.2 ⟨IJ, λ h, hJ (hI.2 _ h)⟩

theorem is_maximal.exists_inv {I : ideal α}
  (hI : I.is_maximal) {x} (hx : x ∉ I) : ∃ y, y * x - 1 ∈ I :=
begin
  cases is_maximal_iff.1 hI with H₁ H₂,
  rcases mem_span_insert'.1 (H₂ (span (insert x I)) x
    (set.subset.trans (subset_insert _ _) subset_span)
    hx (subset_span (mem_insert _ _))) with ⟨y, hy⟩,
  rw [span_eq, ← neg_mem_iff, add_comm, neg_add', neg_mul_eq_neg_mul] at hy,
  exact ⟨-y, hy⟩
end

theorem is_maximal.is_prime {I : ideal α} (H : I.is_maximal) : I.is_prime :=
⟨H.1, λ x y hxy, or_iff_not_imp_left.2 $ λ hx, begin
  cases H.exists_inv hx with z hz,
  have := I.mul_mem_left hz,
  rw [mul_sub, mul_one, mul_comm, mul_assoc] at this,
  exact I.neg_mem_iff.1 ((I.add_mem_iff_right $ I.mul_mem_left hxy).1 this)
end⟩

instance is_maximal.is_prime' (I : ideal α) : ∀ [H : I.is_maximal], I.is_prime := is_maximal.is_prime

theorem exists_le_maximal (I : ideal α) (hI : I ≠ ⊤) :
  ∃ M : ideal α, M.is_maximal ∧ I ≤ M :=
begin
  rcases zorn.zorn_partial_order₀ { J : ideal α | J ≠ ⊤ } _ I hI with ⟨M, M0, IM, h⟩,
  { refine ⟨M, ⟨M0, λ J hJ, by_contradiction $ λ J0, _⟩, IM⟩,
    cases h J J0 (le_of_lt hJ), exact lt_irrefl _ hJ },
  { intros S SC cC I IS,
    refine ⟨Sup S, λ H, _, λ _, le_Sup⟩,
    rcases submodule.mem_Sup_of_directed ((eq_top_iff_one _).1 H) I IS cC.directed_on with ⟨J, JS, J0⟩,
    exact SC JS ((eq_top_iff_one _).2 J0) }
end

def is_coprime (x y : α) : Prop :=
span ({x, y} : set α) = ⊤

theorem mem_span_pair {α} [comm_ring α] {x y z : α} :
  z ∈ span (insert y {x} : set α) ↔ ∃ a b, a * x + b * y = z :=
begin
  simp only [mem_span_insert, mem_span_singleton', exists_prop],
  split,
  { rintros ⟨a, b, ⟨c, hc⟩, h⟩,
    exact ⟨c, a, by simp [h, hc]⟩ },
  { rintro ⟨b, c, e⟩, exact ⟨c, b * x, ⟨b, rfl⟩, by simp [e.symm]⟩ }
end

theorem is_coprime_def {α} [comm_ring α] {x y : α} :
  is_coprime x y ↔ ∀ z, ∃ a b, a * x + b * y = z :=
by simp [is_coprime, submodule.eq_top_iff', mem_span_pair]

theorem is_coprime_self {α} [comm_ring α] (x y : α) :
  is_coprime x x ↔ is_unit x :=
by rw [← span_singleton_eq_top]; simp [is_coprime]

lemma span_singleton_lt_span_singleton [integral_domain β] {x y : β} :
  span ({x} : set β) < span ({y} : set β) ↔ y ≠ 0 ∧ ∃ d : β, ¬ is_unit d ∧ x = y * d :=
by rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
  dvd_and_not_dvd_iff]

end ideal

def nonunits (α : Type u) [monoid α] : set α := { x | ¬is_unit x }

@[simp] theorem mem_nonunits_iff {α} [comm_monoid α] {x} : x ∈ nonunits α ↔ ¬ is_unit x := iff.rfl

theorem mul_mem_nonunits_right {α} [comm_monoid α]
  {x y : α} : y ∈ nonunits α → x * y ∈ nonunits α :=
mt is_unit_of_mul_is_unit_right

theorem mul_mem_nonunits_left {α} [comm_monoid α]
  {x y : α} : x ∈ nonunits α → x * y ∈ nonunits α :=
mt is_unit_of_mul_is_unit_left

theorem zero_mem_nonunits {α} [semiring α] : 0 ∈ nonunits α ↔ (0:α) ≠ 1 :=
not_congr is_unit_zero_iff

theorem one_not_mem_nonunits {α} [monoid α] : (1:α) ∉ nonunits α :=
not_not_intro is_unit_one

theorem coe_subset_nonunits {I : ideal α} (h : I ≠ ⊤) :
  (I : set α) ⊆ nonunits α :=
λ x hx hu, h $ I.eq_top_of_is_unit_mem hx hu

@[class] def is_local_ring (α : Type u) [comm_ring α] : Prop :=
∃! I : ideal α, I.is_maximal

@[class] def is_local_ring.zero_ne_one (h : is_local_ring α) : (0:α) ≠ 1 :=
let ⟨I, ⟨hI, _⟩, _⟩ := h in ideal.zero_ne_one_of_proper hI

def nonunits_ideal (h : is_local_ring α) : ideal α :=
{ carrier := nonunits α,
  zero := zero_mem_nonunits.2 h.zero_ne_one,
  add := begin
    rcases id h with ⟨M, mM, hM⟩,
    have : ∀ x ∈ nonunits α, x ∈ M,
    { intros x hx,
      rcases (ideal.span {x} : ideal α).exists_le_maximal _ with ⟨N, mN, hN⟩,
      { cases hM N mN,
        rwa [ideal.span_le, singleton_subset_iff] at hN },
      { exact mt ideal.span_singleton_eq_top.1 hx } },
    intros x y hx hy,
    exact coe_subset_nonunits mM.1 (M.add_mem (this _ hx) (this _ hy))
  end,
  smul := λ a x, mul_mem_nonunits_right }

@[simp] theorem mem_nonunits_ideal (h : is_local_ring α) {x} :
  x ∈ nonunits_ideal h ↔ x ∈ nonunits α := iff.rfl

theorem local_of_nonunits_ideal (hnze : (0:α) ≠ 1)
  (h : ∀ x y ∈ nonunits α, x + y ∈ nonunits α) : is_local_ring α :=
begin
  letI NU : ideal α := ⟨nonunits α,
    zero_mem_nonunits.2 hnze, h, λ a x, mul_mem_nonunits_right⟩,
  have NU1 := NU.ne_top_iff_one.2 one_not_mem_nonunits,
  exact ⟨NU, ⟨NU1,
    λ J hJ, not_not.1 $ λ J0, not_le_of_gt hJ (coe_subset_nonunits J0)⟩,
    λ J mJ, mJ.eq_of_le NU1 (coe_subset_nonunits mJ.1)⟩,
end

namespace ideal
open ideal

def quotient (I : ideal α) := I.quotient

namespace quotient
variables {I : ideal α} {x y : α}
def mk (I : ideal α) (a : α) : I.quotient := submodule.quotient.mk a

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I := submodule.quotient.eq I

instance (I : ideal α) : has_one I.quotient := ⟨mk I 1⟩

@[simp] lemma mk_one (I : ideal α) : mk I 1 = 1 := rfl

instance (I : ideal α) : has_mul I.quotient :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk I (a * b)) $
 λ a₁ a₂ b₁ b₂ h₁ h₂, quot.sound $ begin
  refine calc a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ : _
  ... ∈ I : I.add_mem (I.mul_mem_left h₁) (I.mul_mem_right h₂),
  rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁]
 end⟩

@[simp] theorem mk_mul : mk I (x * y) = mk I x * mk I y := rfl

instance (I : ideal α) : comm_ring I.quotient :=
{ mul := (*),
  one := 1,
  mul_assoc := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg (mk _) (mul_assoc a b c),
  mul_comm := λ a b, quotient.induction_on₂' a b $
    λ a b, congr_arg (mk _) (mul_comm a b),
  one_mul := λ a, quotient.induction_on' a $
    λ a, congr_arg (mk _) (one_mul a),
  mul_one := λ a, quotient.induction_on' a $
    λ a, congr_arg (mk _) (mul_one a),
  left_distrib := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg (mk _) (left_distrib a b c),
  right_distrib := λ a b c, quotient.induction_on₃' a b c $
    λ a b c, congr_arg (mk _) (right_distrib a b c),
  ..submodule.quotient.add_comm_group I }

instance is_ring_hom_mk (I : ideal α) : is_ring_hom (mk I) :=
⟨rfl, λ _ _, rfl, λ _ _, rfl⟩

def map_mk (I J : ideal α) : ideal I.quotient :=
{ carrier := mk I '' J,
  zero := ⟨0, J.zero_mem, rfl⟩,
  add := by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩;
    exact ⟨x + y, J.add_mem hx hy, rfl⟩,
  smul := by rintro ⟨c⟩ _ ⟨x, hx, rfl⟩;
    exact ⟨c * x, J.mul_mem_left hx, rfl⟩ }

@[simp] lemma mk_zero (I : ideal α) : mk I 0 = 0 := rfl
@[simp] lemma mk_add (I : ideal α) (a b : α) : mk I (a + b) = mk I a + mk I b := rfl
@[simp] lemma mk_neg (I : ideal α) (a : α) : mk I (-a : α) = -mk I a := rfl
@[simp] lemma mk_sub (I : ideal α) (a b : α) : mk I (a - b : α) = mk I a - mk I b := rfl
@[simp] lemma mk_pow (I : ideal α) (a : α) (n : ℕ) : mk I (a ^ n : α) = mk I a ^ n :=
by induction n; simp [*, pow_succ]

lemma eq_zero_iff_mem {I : ideal α} : mk I a = 0 ↔ a ∈ I :=
by conv {to_rhs, rw ← sub_zero a }; exact quotient.eq'

theorem zero_eq_one_iff {I : ideal α} : (0 : I.quotient) = 1 ↔ I = ⊤ :=
eq_comm.trans $ eq_zero_iff_mem.trans (eq_top_iff_one _).symm

theorem zero_ne_one_iff {I : ideal α} : (0 : I.quotient) ≠ 1 ↔ I ≠ ⊤ :=
not_congr zero_eq_one_iff

protected def nonzero_comm_ring {I : ideal α} (hI : I ≠ ⊤) : nonzero_comm_ring I.quotient :=
{ zero_ne_one := zero_ne_one_iff.2 hI, ..quotient.comm_ring I }

instance (I : ideal α) [hI : I.is_prime] : integral_domain I.quotient :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,
    quotient.induction_on₂' a b $ λ a b hab,
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim
        (or.inl ∘ eq_zero_iff_mem.2)
        (or.inr ∘ eq_zero_iff_mem.2),
  ..quotient.nonzero_comm_ring hI.1 }

lemma exists_inv {I : ideal α} [hI : I.is_maximal] :
 ∀ {a : I.quotient}, a ≠ 0 → ∃ b : I.quotient, a * b = 1 :=
begin
  rintro ⟨a⟩ h,
  cases hI.exists_inv (mt eq_zero_iff_mem.2 h) with b hb,
  rw [mul_comm] at hb,
  exact ⟨mk _ b, quot.sound hb⟩
end

/-- quotient by maximal ideal is a field. def rather than instance, since users will have
computable inverses in some applications -/
protected noncomputable def field (I : ideal α) [hI : I.is_maximal] : field I.quotient :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (exists_inv ha),
  mul_inv_cancel := λ a (ha : a ≠ 0), show a * dite _ _ _ = _,
    by rw dif_neg ha;
    exact classical.some_spec (exists_inv ha),
  inv_mul_cancel := λ a (ha : a ≠ 0), show dite _ _ _ * a = _,
    by rw [mul_comm, dif_neg ha];
    exact classical.some_spec (exists_inv ha),
  ..quotient.integral_domain I }

variable [comm_ring β]

def lift (S : ideal α) (f : α → β) [is_ring_hom f] (H : ∀ (a : α), a ∈ S → f a = 0) :
  quotient S → β :=
λ x, quotient.lift_on' x f $ λ (a b) (h : _ ∈ _),
eq_of_sub_eq_zero (by simpa only [is_ring_hom.map_sub f] using H _ h)

variables {S : ideal α} {f : α → β} [is_ring_hom f] {H : ∀ (a : α), a ∈ S → f a = 0}

@[simp] lemma lift_mk : lift S f H (mk S a) = f a := rfl

instance : is_ring_hom (lift S f H) :=
{ map_one := by show lift S f H (mk S 1) = 1; simp [is_ring_hom.map_one f, - mk_one],
  map_add := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk S a₁ + mk S a₂) = lift S f H (mk S a₁) + lift S f H (mk S a₂),
    have := ideal.quotient.is_ring_hom_mk S,
    rw ← this.map_add,
    show lift S f H (mk S (a₁ + a₂)) = lift S f H (mk S a₁) + lift S f H (mk S a₂),
    simp only [lift_mk, is_ring_hom.map_add f],
  end,
  map_mul := λ a₁ a₂, quotient.induction_on₂' a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk S a₁ * mk S a₂) = lift S f H (mk S a₁) * lift S f H (mk S a₂),
    have := ideal.quotient.is_ring_hom_mk S,
    rw ← this.map_mul,
    show lift S f H (mk S (a₁ * a₂)) = lift S f H (mk S a₁) * lift S f H (mk S a₂),
    simp only [lift_mk, is_ring_hom.map_mul f],
  end }

end quotient
end ideal
