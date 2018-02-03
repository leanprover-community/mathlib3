import algebra.ring data.set.basic tactic.ring data.quot

universe u

namespace loc

variables (α : Type u) [comm_ring α] (S : set α)

class is_submonoid : Prop :=
(one_mem : (1:α) ∈ S)
(mul_mem : ∀ {s t}, s ∈ S → t ∈ S → s*t ∈ S)

variable [is_submonoid α S]

def r : α × S → α × S → Prop :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ∃ t ∈ S, t * (r₁ * s₂ - r₂ * s₁) = 0

local infix ≈ := r α S

theorem refl : ∀ (x : α × S), x ≈ x :=
λ ⟨r₁, s₁, hs₁⟩, ⟨1, is_submonoid.one_mem S, by simp⟩

theorem symm : ∀ (x y : α × S), x ≈ y → y ≈ x :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩, ⟨t, hts, calc
        t * (r₂ * s₁ - r₁ * s₂)
      = -(t * (r₁ * s₂ - r₂ * s₁)) : by simp [mul_add]
  ... = 0 : by rw ht; simp⟩

theorem trans : ∀ (x y z : α × S), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
⟨t * t' * s₂, is_submonoid.mul_mem (is_submonoid.mul_mem hts hts') hs₂, calc
         t * t' * s₂ * (r₁ * s₃ - r₃ * s₁)
       = t' * s₃ * (t * (r₁ * s₂ - r₂ * s₁)) + t * s₁ * (t' * (r₂ * s₃ - r₃ * s₂)) :
           by simp [mul_left_comm, mul_add, mul_comm]
   ... = 0 : by rw [ht, ht']; simp⟩

instance : setoid (α × S) :=
⟨r α S, refl α S, symm α S, trans α S⟩

def loc := quotient $ loc.setoid α S

def add_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def add : loc α S → loc α S → loc α S :=
quotient.lift₂ (add_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * s₂ + r₂ * s₁) * (s₃ * s₄) - (r₃ * s₄ + r₄ * s₃) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * s₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * s₁ * s₃ : by ring
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

def neg_aux : α × S → loc α S :=
λ ⟨r, s, hs⟩, ⟦⟨-r, s, hs⟩⟧

def neg : loc α S → loc α S :=
quotient.lift (neg_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
quotient.sound ⟨t, hts, calc
        t * (-r₁ * s₂ - -r₂ * s₁)
      = -(t * (r₁ * s₂ - r₂ * s₁)) : by ring
  ... = 0 : by rw ht; simp⟩

def mul_aux : α × S → α × S → loc α S :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ⟦⟨r₁ * r₂, s₁ * s₂, is_submonoid.mul_mem hs₁ hs₂⟩⟧

def mul : loc α S → loc α S → loc α S :=
quotient.lift₂ (mul_aux α S) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
quotient.sound ⟨t₅ * t₆, is_submonoid.mul_mem hts₅ hts₆, calc
        t₅ * t₆ * ((r₁ * r₂) * (s₃ * s₄) - (r₃ * r₄) * (s₁ * s₂))
      = t₆ * (t₅ * (r₁ * s₃ - r₃ * s₁)) * r₂ * s₄ + t₅ * (t₆ * (r₂ * s₄ - r₄ * s₂)) * r₃ * s₁ : by simp [mul_left_comm, mul_add, mul_comm]
  ... = 0 : by rw [ht₅, ht₆]; simp⟩

instance : comm_ring (loc α S) :=
by refine
{ add            := add α S,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := ⟦⟨0, 1, is_submonoid.one_mem S⟩⟧,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := neg α S,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := mul α S,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := ⟦⟨1, 1, is_submonoid.one_mem S⟩⟧,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {cases a with r₁ s₁, cases s₁ with s₁ hs₁},
  try {cases b with r₂ s₂, cases s₂ with s₂ hs₂},
  try {cases c with r₃ s₃, cases s₃ with s₃ hs₃},
  apply quotient.sound,
  existsi (1:α),
  existsi is_submonoid.one_mem S,
  simp [mul_left_comm, mul_add, mul_comm] }

def of_comm_ring : α → loc α S :=
λ r, ⟦⟨r, 1, is_submonoid.one_mem S⟩⟧

instance : is_hom (of_comm_ring α S) :=
{ map_add := λ x y, quotient.sound $ by simp,
  map_mul := λ x y, quotient.sound $ by simp,
  map_one := rfl }

local infix ^ := monoid.pow

variable {α}

def powers (x : α) : set α := {y | ∃ n, x^n = y}

instance powers.is_submonoid (x : α) : is_submonoid α (powers x) :=
{ one_mem := ⟨0, by simp⟩,
  mul_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [pow_add, *]⟩ }

def away (x : α) := loc α (powers x)

section at_prime

variables (P : set α) [is_prime_ideal P]

instance prime.is_submonoid :
  is_submonoid α (set.compl P) :=
{ one_mem := λ h, is_prime_ideal.ne_univ_ideal P $
    is_ideal.univ_of_one_mem P h,
  mul_mem := λ x y hnx hny hxy, or.cases_on
    (is_prime_ideal.mem_or_mem_of_mul_mem hxy) hnx hny }

def at_prime := loc α (set.compl P)

instance at_prime.local_ring :
  @local_ring (at_prime P) (loc.comm_ring α _) :=
local_of_nonunits_ideal
  (λ hze, have _, from quotient.exact hze, let ⟨t, hts, ht⟩ := this in
     hts $ have htz : t = 0, by simpa using ht,
       suffices (0:α) ∈ P, by rwa htz,
       is_ideal.zero_mem P)
  (λ x y hx hy ⟨z, hz⟩,
     let ⟨⟨r₁, s₁, hs₁⟩, hrs₁⟩ := quotient.exists_rep x,
         ⟨⟨r₂, s₂, hs₂⟩, hrs₂⟩ := quotient.exists_rep y,
         ⟨⟨r₃, s₃, hs₃⟩, hrs₃⟩ := quotient.exists_rep z in
     have _, by rw [← hrs₁, ← hrs₂, ← hrs₃] at hz; from quotient.exact hz,
     let ⟨t, hts, ht⟩ := this in
     have hr₁ : r₁ ∈ P, from classical.by_contradiction $
     λ hnr₁, hx ⟨⟦⟨s₁, r₁, hnr₁⟩⟧, by rw ←hrs₁;
       from quotient.sound ⟨1, is_submonoid.one_mem _, by simp [mul_comm]⟩⟩,
     have hr₂ : r₂ ∈ P, from classical.by_contradiction $
     λ hnr₂, hy ⟨⟦⟨s₂, r₂, hnr₂⟩⟧, by rw ←hrs₂;
       from quotient.sound ⟨1, is_submonoid.one_mem _, by simp [mul_comm]⟩⟩,
     or.cases_on (mem_or_mem_of_mul_eq_zero P ht) hts $
     λ h, have h1 : (r₁ * s₂ + r₂ * s₁) * r₃ - s₁ * s₂ * s₃ ∈ P,
     by simpa using h,
     have h2 : (r₁ * s₂ + r₂ * s₁) * r₃ ∈ P,
     from is_ideal.mul_mem $ is_ideal.add_mem
         (is_ideal.mul_mem hr₁)
         (is_ideal.mul_mem hr₂),
     or.cases_on (is_prime_ideal.mem_or_mem_of_mul_mem $
         is_ideal.mem_of_mem_of_sub_mem h2 h1)
       (λ h3, or.cases_on (is_prime_ideal.mem_or_mem_of_mul_mem h3) hs₁ hs₂)
       hs₃)

end at_prime

def closure (S : set α) : set α := {y | ∃ (L:list α) (H:∀ x ∈ L, x ∈ S), L.prod = y }

instance closure.is_submonoid (S : set α) : is_submonoid α (closure S) :=
{ one_mem := ⟨[], by simp⟩,
  mul_mem := λ x₁ x₂ ⟨L₁, hLS₁, hL₁⟩ ⟨L₂, hLS₂, hL₂⟩,
    ⟨L₁ ++ L₂,
     λ x hx, or.cases_on (list.mem_append.1 hx) (hLS₁ x) (hLS₂ x),
     by simp [list.prod_append, *]⟩ }

variable α

def non_zero_divisors : set α := {x | ∀ z, x * z = 0 → z = 0}

instance non_zero_divisors.is_submonoid : is_submonoid α (non_zero_divisors α) :=
{ one_mem := λ z hz, by simpa using hz,
  mul_mem := λ x₁ x₂ hx₁ hx₂ z hz,
    have x₁ * (x₂ * z) = 0,
    by rwa mul_assoc at hz,
    hx₂ z $ hx₁ (x₂ * z) this }

def quotient_ring := loc α (non_zero_divisors α)

section quotient_ring

variables {β : Type u} [integral_domain β] [decidable_eq β]

lemma ne_zero_of_mem_non_zero_divisors {x : β} :
  x ∈ loc.non_zero_divisors β → x ≠ 0 :=
λ hm hz, have x * 1 = 0, by simp [hz], zero_ne_one (hm 1 this).symm

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} : x ≠ 0 → x * y = 0 → y = 0 :=
λ hnx hxy, match eq_zero_or_eq_zero_of_mul_eq_zero hxy with
| or.inl hx := false.elim $ hnx hx
| or.inr hy := hy
end

lemma mem_non_zero_divisors_of_ne_zero {x : β} :
  x ≠ 0 → x ∈ loc.non_zero_divisors β :=
λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx

variable β

def inv_aux : β × (non_zero_divisors β) → quotient_ring β :=
λ ⟨r, s, hs⟩, if h : r = 0 then
  ⟦⟨0, 1, is_submonoid.one_mem _⟩⟧
else ⟦⟨s, r, mem_non_zero_divisors_of_ne_zero h⟩⟧

def inv : quotient_ring β → quotient_ring β :=
quotient.lift (inv_aux β) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
begin
  have hrs : r₁ * s₂ - r₂ * s₁ = 0,
  { from hts _ ht },
  by_cases hr₁ : r₁ = 0;
  by_cases hr₂ : r₂ = 0;
  simp [inv_aux, hr₁, hr₂],
  { exfalso,
    simp [hr₁] at hrs,
    exact ne_zero_of_mem_non_zero_divisors hs₁
      (eq_zero_of_ne_zero_of_mul_eq_zero hr₂ hrs) },
  { exfalso,
    simp [hr₂] at hrs,
    exact ne_zero_of_mem_non_zero_divisors hs₂
      (eq_zero_of_ne_zero_of_mul_eq_zero hr₁ hrs) },
  { exact ⟨1, is_submonoid.one_mem _,
    by simpa [mul_comm] using congr_arg (λ x, -x) hrs⟩ }
end

instance quotient_ring.field.of_integral_domain : field (quotient_ring β) :=
by refine
{ loc.comm_ring β _ with
  inv := inv β,
  zero_ne_one := λ hzo, let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_mul_cancel := quotient.ind _ };
{ intros x hnx,
  cases x with x hx,
  cases hx with z hz,
  have : x ≠ 0,
    intro hx,
    apply hnx,
    apply quotient.sound,
    existsi (1:β),
    existsi is_submonoid.one_mem _,
    simp [hx],
    exact non_zero_divisors.is_submonoid β,
  simp [inv, inv_aux, inv_aux._match_1],
  rw dif_neg this,
  apply quotient.sound,
  existsi (1:β),
  existsi is_submonoid.one_mem _,
  ring,
  exact non_zero_divisors.is_submonoid β }

end quotient_ring

end loc
