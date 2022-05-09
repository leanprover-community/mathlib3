/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import data.nat.enat
import data.set.countable
import logic.small
import order.conditionally_complete_lattice
import set_theory.schroeder_bernstein

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* There is an instance that `cardinal` forms a `canonically_ordered_comm_semiring`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.omega` or `ω` the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.omega.{u} : cardinal.{u}`
  (contrast with `ℕ : Type`, which lives in a specific universe).
  In some cases the universe level has to be given explicitly.
* `cardinal.min (I : nonempty ι) (c : ι → cardinal)` is the minimal cardinal in the range of `c`.
* `cardinal.succ c` is the successor cardinal, the smallest cardinal larger than `c`.
* `cardinal.sum` is the sum of a collection of cardinals.
* `cardinal.sup` is the supremum of a collection of cardinals.
* `cardinal.powerlt c₁ c₂` or `c₁ ^< c₂` is defined as `sup_{γ < β} α^γ`.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, omega,
Cantor's theorem, König's theorem, Konig's theorem
-/

open function set
open_locale classical

noncomputable theory

universes u v w x
variables {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λ α β, nonempty (α ≃ β),
  iseqv := ⟨λ α,
    ⟨equiv.refl α⟩,
    λ α β ⟨e⟩, ⟨e.symm⟩,
    λ α β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

/-- The cardinal number of a type -/
def mk : Type u → cardinal := quotient.mk

localized "notation `#` := cardinal.mk" in cardinal

instance can_lift_cardinal_Type : can_lift cardinal.{u} (Type u) :=
⟨mk, λ c, true, λ c _, quot.induction_on c $ λ α, ⟨α, rfl⟩⟩

@[elab_as_eliminator]
lemma induction_on {p : cardinal → Prop} (c : cardinal) (h : ∀ α, p (#α)) : p c :=
quotient.induction_on c h

@[elab_as_eliminator]
lemma induction_on₂ {p : cardinal → cardinal → Prop} (c₁ : cardinal) (c₂ : cardinal)
  (h : ∀ α β, p (#α) (#β)) : p c₁ c₂ :=
quotient.induction_on₂ c₁ c₂ h

@[elab_as_eliminator]
lemma induction_on₃ {p : cardinal → cardinal → cardinal → Prop} (c₁ : cardinal) (c₂ : cardinal)
  (c₃ : cardinal) (h : ∀ α β γ, p (#α) (#β) (#γ)) : p c₁ c₂ c₃ :=
quotient.induction_on₃ c₁ c₂ c₃ h

protected lemma eq : #α = #β ↔ nonempty (α ≃ β) := quotient.eq

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ (#α) := rfl

@[simp] theorem mk_out (c : cardinal) : #(c.out) = c := quotient.out_eq _

/-- The representative of the cardinal of a type is equivalent ot the original type. -/
def out_mk_equiv {α : Type v} : (#α).out ≃ α :=
nonempty.some $ cardinal.eq.mp (by simp)

lemma mk_congr (e : α ≃ β) : # α = # β := quot.sound ⟨e⟩

alias mk_congr ← equiv.cardinal_eq

/-- Lift a function between `Type*`s to a function between `cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) :
  cardinal.{u} → cardinal.{v} :=
quotient.map f (λ α β ⟨e⟩, ⟨hf α β e⟩)

@[simp] lemma map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
  map f hf (#α) = #(f α) := rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
  cardinal.{u} → cardinal.{v} → cardinal.{w} :=
quotient.map₂ f $ λ α β ⟨e₁⟩ γ δ ⟨e₂⟩, ⟨hf α β γ δ e₁ e₂⟩

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{v} → cardinal.{max v u}` -/
def lift (c : cardinal.{v}) : cardinal.{max v u} :=
map ulift (λ α β e, equiv.ulift.trans $ e.trans equiv.ulift.symm) c

@[simp] theorem mk_ulift (α) : #(ulift.{v u} α) = lift.{v} (#α) := rfl

theorem lift_umax : lift.{(max u v) u} = lift.{v u} :=
funext $ λ a, induction_on a $ λ α, (equiv.ulift.trans equiv.ulift.symm).cardinal_eq

theorem lift_umax' : lift.{(max v u) u} = lift.{v u} := lift_umax

theorem lift_id' (a : cardinal.{max u v}) : lift.{u} a = a :=
induction_on a $ λ α, mk_congr equiv.ulift

@[simp] theorem lift_id (a : cardinal) : lift.{u u} a = a := lift_id'.{u u} a
@[simp] theorem lift_uzero (a : cardinal.{u}) : lift.{0} a = a := lift_id'.{0 u} a

@[simp] theorem lift_lift (a : cardinal) :
  lift.{w} (lift.{v} a) = lift.{(max v w)} a :=
induction_on a $ λ α,
(equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm).cardinal_eq

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : has_le cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, nonempty $ α ↪ β) $
  assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
    propext ⟨assume ⟨e⟩, ⟨e.congr e₁ e₂⟩, assume ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

theorem le_def (α β : Type u) : #α ≤ #β ↔ nonempty (α ↪ β) :=
iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : injective f) : #α ≤ #β :=
⟨⟨f, hf⟩⟩

theorem _root_.function.embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β := ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : surjective f) : #β ≤ #α :=
⟨embedding.of_surjective f hf⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ #α ↔ ∃ p : set α, #p = c :=
⟨induction_on c $ λ β ⟨⟨f, hf⟩⟩,
  ⟨set.range f, (equiv.of_injective f hf).cardinal_eq.symm⟩,
λ ⟨p, e⟩, e ▸ ⟨⟨subtype.val, λ a b, subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(subtype p) ≤ #α :=
⟨embedding.subtype p⟩

theorem mk_set_le (s : set α) : #s ≤ #α :=
mk_subtype_le s

theorem out_embedding {c c' : cardinal} : c ≤ c' ↔ nonempty (c.out ↪ c'.out) :=
by { transitivity _, rw [←quotient.out_eq c, ←quotient.out_eq c'], refl }

instance : preorder cardinal.{u} :=
{ le          := (≤),
  le_refl     := by rintros ⟨α⟩; exact ⟨embedding.refl _⟩,
  le_trans    := by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.trans e₂⟩ }

instance : partial_order cardinal.{u} :=
{ le_antisymm := by { rintros ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩, exact quotient.sound (e₁.antisymm e₂) },
  .. cardinal.preorder }

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{(max v w)} (#α) ≤ lift.{(max u w)} (#β) ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

/-- A variant of `cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} :
  lift.{v} (#α) ≤ lift.{u} (#β) ↔ nonempty (α ↪ β) :=
lift_mk_le.{u v 0}

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{(max v w)} (#α) = lift.{(max u w)} (#β) ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans $ f.trans equiv.ulift⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans $ f.trans equiv.ulift.symm⟩⟩

/-- A variant of `cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} :
  lift.{v} (#α) = lift.{u} (#β) ↔ nonempty (α ≃ β) :=
lift_mk_eq.{u v 0}

@[simp] theorem lift_le {a b : cardinal} : lift a ≤ lift b ↔ a ≤ b :=
induction_on₂ a b $ λ α β, by { rw ← lift_umax, exact lift_mk_le }

/-- `cardinal.lift` as an `order_embedding`. -/
@[simps { fully_applied := ff }] def lift_order_embedding : cardinal.{v} ↪o cardinal.{max v u} :=
order_embedding.of_map_le_iff lift (λ _ _, lift_le)

theorem lift_injective : injective lift.{u v} := lift_order_embedding.injective

@[simp] theorem lift_inj {a b : cardinal} : lift a = lift b ↔ a = b :=
lift_injective.eq_iff

@[simp] theorem lift_lt {a b : cardinal} : lift a < lift b ↔ a < b :=
lift_order_embedding.lt_iff_lt

instance : has_zero cardinal.{u} := ⟨#pempty⟩

instance : inhabited cardinal.{u} := ⟨0⟩

lemma mk_eq_zero (α : Type u) [is_empty α] : #α = 0 :=
(equiv.equiv_pempty α).cardinal_eq

@[simp] theorem lift_zero : lift 0 = 0 := mk_congr (equiv.equiv_pempty _)

@[simp] theorem lift_eq_zero {a : cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
lift_injective.eq_iff' lift_zero

lemma mk_eq_zero_iff {α : Type u} : #α = 0 ↔ is_empty α :=
⟨λ e, let ⟨h⟩ := quotient.exact e in h.is_empty, @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ nonempty α :=
(not_iff_not.2 mk_eq_zero_iff).trans not_is_empty_iff

@[simp] lemma mk_ne_zero (α : Type u) [nonempty α] : #α ≠ 0 := mk_ne_zero_iff.2 ‹_›

instance : has_one cardinal.{u} := ⟨⟦punit⟧⟩

instance : nontrivial cardinal.{u} := ⟨⟨1, 0, mk_ne_zero _⟩⟩

lemma mk_eq_one (α : Type u) [unique α] : #α = 1 :=
mk_congr equiv_punit_of_unique

theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a b, f.injective (subsingleton.elim _ _)⟩,
 λ ⟨h⟩, ⟨⟨λ a, punit.star, λ a b _, h _ _⟩⟩⟩

instance : has_add cardinal.{u} := ⟨map₂ sum $ λ α β γ δ, equiv.sum_congr⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) := rfl

@[simp] lemma mk_sum (α : Type u) (β : Type v) :
  #(α ⊕ β) = lift.{v u} (#α) + lift.{u v} (#β) :=
mk_congr ((equiv.ulift).symm.sum_congr (equiv.ulift).symm)

@[simp] theorem mk_option {α : Type u} : #(option α) = #α + 1 :=
(equiv.option_equiv_sum_punit α).cardinal_eq

@[simp] lemma mk_psum (α : Type u) (β : Type v) : #(psum α β) = lift.{v} (#α) + lift.{u} (#β) :=
(mk_congr (equiv.psum_equiv_sum α β)).trans (mk_sum α β)

@[simp] lemma mk_fintype (α : Type u) [fintype α] : #α = fintype.card α :=
begin
  refine fintype.induction_empty_option' _ _ _ α,
  { introsI α β h e hα, letI := fintype.of_equiv β e.symm,
    rwa [mk_congr e, fintype.card_congr e] at hα },
  { refl },
  { introsI α h hα, simp [hα] }
end

instance : has_mul cardinal.{u} := ⟨map₂ prod $ λ α β γ δ, equiv.prod_congr⟩

theorem mul_def (α β : Type u) : #α * #β = #(α × β) := rfl

@[simp] lemma mk_prod (α : Type u) (β : Type v) :
  #(α × β) = lift.{v u} (#α) * lift.{u v} (#β) :=
mk_congr (equiv.ulift.symm.prod_congr (equiv.ulift).symm)

protected theorem add_comm (a b : cardinal.{u}) : a + b = b + a :=
induction_on₂ a b $ λ α β, mk_congr (equiv.sum_comm α β)

protected theorem mul_comm (a b : cardinal.{u}) : a * b = b * a :=
induction_on₂ a b $ λ α β, mk_congr (equiv.prod_comm α β)

protected theorem zero_add (a : cardinal.{u}) : 0 + a = a :=
induction_on a $ λ α, mk_congr (equiv.empty_sum pempty α)

protected theorem zero_mul (a : cardinal.{u}) : 0 * a = 0 :=
induction_on a $ λ α, mk_congr (equiv.pempty_prod α)

protected theorem one_mul (a : cardinal.{u}) : 1 * a = a :=
induction_on a $ λ α, mk_congr (equiv.punit_prod α)

protected theorem left_distrib (a b c : cardinal.{u}) : a * (b + c) = a * b + a * c :=
induction_on₃ a b c $ λ α β γ, mk_congr (equiv.prod_sum_distrib α β γ)

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : cardinal.{u}} :
  a * b = 0 → a = 0 ∨ b = 0 :=
begin
  induction a using cardinal.induction_on with α,
  induction b using cardinal.induction_on with β,
  simp only [mul_def, mk_eq_zero_iff, is_empty_prod],
  exact id
end

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
protected def power (a b : cardinal.{u}) : cardinal.{u} :=
map₂ (λ α β : Type u, β → α) (λ α β γ δ e₁ e₂, e₂.arrow_congr e₁) a b

instance : has_pow cardinal cardinal := ⟨cardinal.power⟩
local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
local infixr ` ^ℕ `:80 := @has_pow.pow cardinal ℕ monoid.has_pow

theorem power_def (α β) : #α ^ #β = #(β → α) := rfl

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = lift.{u} (#β) ^ lift.{v} (#α) :=
mk_congr (equiv.ulift.symm.arrow_congr equiv.ulift.symm)

@[simp] theorem lift_power (a b) : lift (a ^ b) = lift a ^ lift b :=
induction_on₂ a b $ λ α β,
mk_congr (equiv.ulift.trans (equiv.ulift.arrow_congr equiv.ulift).symm)

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
induction_on a $ assume α, (equiv.pempty_arrow_equiv_punit α).cardinal_eq

@[simp] theorem power_one {a : cardinal} : a ^ 1 = a :=
induction_on a $ assume α, (equiv.punit_arrow_equiv α).cardinal_eq

theorem power_add {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
induction_on₃ a b c $ assume α β γ, (equiv.sum_arrow_equiv_prod_arrow β γ α).cardinal_eq

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := cardinal.zero_add,
  add_zero      := assume a, by rw [cardinal.add_comm a 0, cardinal.zero_add a],
  add_assoc     := λa b c, induction_on₃ a b c $ assume α β γ, mk_congr (equiv.sum_assoc α β γ),
  add_comm      := cardinal.add_comm,
  zero_mul      := cardinal.zero_mul,
  mul_zero      := assume a, by rw [cardinal.mul_comm a 0, cardinal.zero_mul a],
  one_mul       := cardinal.one_mul,
  mul_one       := assume a, by rw [cardinal.mul_comm a 1, cardinal.one_mul a],
  mul_assoc     := λa b c, induction_on₃ a b c $ assume α β γ, mk_congr (equiv.prod_assoc α β γ),
  mul_comm      := cardinal.mul_comm,
  left_distrib  := cardinal.left_distrib,
  right_distrib := assume a b c, by rw [cardinal.mul_comm (a + b) c, cardinal.left_distrib c a b,
    cardinal.mul_comm c a, cardinal.mul_comm c b],
  npow          := λ n c, c ^ n,
  npow_zero'    := @power_zero,
  npow_succ'    := λ n c, by rw [nat.cast_succ, power_add, power_one, cardinal.mul_comm] }

theorem power_bit0 (a b : cardinal) : a ^ (bit0 b) = a ^ b * a ^ b :=
power_add

theorem power_bit1 (a b : cardinal) : a ^ (bit1 b) = a ^ b * a ^ b * a :=
by rw [bit1, ←power_bit0, power_add, power_one]

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
induction_on a $ assume α, (equiv.arrow_punit_equiv_punit α).cardinal_eq

@[simp] theorem mk_bool : #bool = 2 := by simp

@[simp] theorem mk_Prop : #(Prop) = 2 := by simp

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
induction_on a $ assume α heq, mk_eq_zero_iff.2 $ is_empty_pi.2 $
let ⟨a⟩ := mk_ne_zero_iff.1 heq in ⟨a, pempty.is_empty⟩

theorem power_ne_zero {a : cardinal} (b) : a ≠ 0 → a ^ b ≠ 0 :=
induction_on₂ a b $ λ α β h,
let ⟨a⟩ := mk_ne_zero_iff.1 h in mk_ne_zero_iff.2 ⟨λ _, a⟩

theorem mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
induction_on₃ a b c $ assume α β γ, (equiv.arrow_prod_equiv_prod_arrow α β γ).cardinal_eq

theorem power_mul {a b c : cardinal} : a ^ (b * c) = (a ^ b) ^ c :=
by rw [mul_comm b c];
from (induction_on₃ a b c $ assume α β γ, mk_congr (equiv.curry γ β α))

@[simp] lemma pow_cast_right (κ : cardinal.{u}) (n : ℕ) :
  (κ ^ (↑n : cardinal.{u})) = κ ^ℕ n :=
rfl

@[simp] theorem lift_one : lift 1 = 1 :=
mk_congr (equiv.ulift.trans equiv.punit_equiv_punit)

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
induction_on₂ a b $ λ α β,
mk_congr (equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm)

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
induction_on₂ a b $ λ α β,
mk_congr (equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm)

@[simp] theorem lift_bit0 (a : cardinal) : lift (bit0 a) = bit0 (lift a) :=
lift_add a a

@[simp] theorem lift_bit1 (a : cardinal) : lift (bit1 a) = bit1 (lift a) :=
by simp [bit1]

theorem lift_two : lift.{u v} 2 = 2 := by simp

@[simp] theorem mk_set {α : Type u} : #(set α) = 2 ^ #α := by simp [set, mk_arrow]

/-- A variant of `cardinal.mk_set` expressed in terms of a `set` instead of a `Type`. -/
@[simp] theorem mk_powerset {α : Type u} (s : set α) : #↥(𝒫 s) = 2 ^ #↥s :=
(mk_congr (equiv.set.powerset s)).trans mk_set

theorem lift_two_power (a) : lift (2 ^ a) = 2 ^ lift a := by simp

section order_properties
open sum

protected theorem zero_le : ∀(a : cardinal), 0 ≤ a :=
by rintro ⟨α⟩; exact ⟨embedding.of_is_empty⟩

protected theorem add_le_add : ∀{a b c d : cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sum_map e₂⟩

protected theorem add_le_add_left (a) {b c : cardinal} : b ≤ c → a + b ≤ a + c :=
cardinal.add_le_add le_rfl

protected theorem le_iff_exists_add {a b : cardinal} : a ≤ b ↔ ∃ c, b = a + c :=
⟨induction_on₂ a b $ λ α β ⟨⟨f, hf⟩⟩,
  have (α ⊕ ((range f)ᶜ : set β)) ≃ β, from
    (equiv.sum_congr (equiv.of_injective f hf) (equiv.refl _)).trans $
    (equiv.set.sum_compl (range f)),
  ⟨#↥(range f)ᶜ, mk_congr this.symm⟩,
 λ ⟨c, e⟩, add_zero a ▸ e.symm ▸ cardinal.add_le_add_left _ (cardinal.zero_le _)⟩

instance : order_bot cardinal.{u} :=
{ bot := 0, bot_le := cardinal.zero_le }

instance : canonically_ordered_comm_semiring cardinal.{u} :=
{ add_le_add_left       := λ a b h c, cardinal.add_le_add_left _ h,
  le_iff_exists_add     := @cardinal.le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := @cardinal.eq_zero_or_eq_zero_of_mul_eq_zero,
  ..cardinal.order_bot,
  ..cardinal.comm_semiring, ..cardinal.partial_order }

@[simp] theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le _) zero_ne_one

lemma zero_power_le (c : cardinal.{u}) : (0 : cardinal.{u}) ^ c ≤ 1 :=
by { by_cases h : c = 0, rw [h, power_zero], rw [zero_power h], apply zero_le }

theorem power_le_power_left : ∀ {a b c : cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩; exact
  let ⟨a⟩ := mk_ne_zero_iff.1 hα in
  ⟨@embedding.arrow_congr_left _ _ _ ⟨a⟩ e⟩

theorem self_le_power (a : cardinal) {b : cardinal} (hb : 1 ≤ b) : a ≤ a ^ b :=
begin
  rcases eq_or_ne a 0 with rfl|ha,
  { exact zero_le _ },
  { convert power_le_power_left ha hb, exact power_one.symm }
end

/-- **Cantor's theorem** -/
theorem cantor (a : cardinal.{u}) : a < 2 ^ a :=
begin
  induction a using cardinal.induction_on with α,
  rw [← mk_set],
  refine ⟨⟨⟨singleton, λ a b, singleton_eq_singleton_iff.1⟩⟩, _⟩,
  rintro ⟨⟨f, hf⟩⟩,
  exact cantor_injective f hf
end

instance : no_max_order cardinal.{u} :=
{ exists_gt := λ a, ⟨_, cantor a⟩, ..cardinal.partial_order }

instance : linear_order cardinal.{u} :=
{ le_total    := by rintros ⟨α⟩ ⟨β⟩; exact embedding.total,
  decidable_le := classical.dec_rel _,
  .. cardinal.partial_order }

instance : canonically_linear_ordered_add_monoid cardinal.{u} :=
{ .. (infer_instance : canonically_ordered_add_monoid cardinal.{u}),
  .. cardinal.linear_order }

-- short-circuit type class inference
instance : distrib_lattice cardinal.{u} := by apply_instance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ nontrivial α :=
by rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, not_not]

theorem power_le_max_power_one {a b c : cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 :=
begin
  by_cases ha : a = 0,
  simp [ha, zero_power_le],
  exact le_trans (power_le_power_left ha h) (le_max_left _ _)
end

theorem power_le_power_right {a b c : cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_right e⟩

end order_properties

/-- The minimum cardinal in a family of cardinals (the existence
  of which is provided by `min_injective`). -/
protected def min {ι} (I : nonempty ι) (f : ι → cardinal) : cardinal :=
f $ classical.some $ @embedding.min_injective _ (λ i, (f i).out) I

theorem min_eq {ι} (I) (f : ι → cardinal) : ∃ i, cardinal.min I f = f i :=
⟨_, rfl⟩

theorem min_le {ι I} (f : ι → cardinal) (i) : cardinal.min I f ≤ f i :=
by rw [← mk_out (cardinal.min I f), ← mk_out (f i)]; exact
let ⟨g⟩ := classical.some_spec
  (@embedding.min_injective _ (λ i, (f i).out) I) in
⟨g i⟩

theorem le_min {ι I} {f : ι → cardinal} {a} : a ≤ cardinal.min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

protected theorem wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h,
  let ι := {c :cardinal // ¬ acc (<) c},
      f : ι → cardinal := subtype.val,
      ⟨⟨c, hc⟩, hi⟩ := @min_eq ι ⟨⟨_, h⟩⟩ f in
    hc (acc.intro _ (λ j ⟨_, h'⟩,
      classical.by_contradiction $ λ hj, h' $
      by have := min_le f ⟨j, hj⟩; rwa hi at this))⟩

instance has_wf : @has_well_founded cardinal.{u} := ⟨(<), cardinal.wf⟩

instance : conditionally_complete_linear_order_bot cardinal :=
cardinal.wf.conditionally_complete_linear_order_with_bot 0 $ le_antisymm (cardinal.zero_le _) $
  not_lt.1 (cardinal.wf.not_lt_min set.univ ⟨0, mem_univ _⟩ (mem_univ 0))

instance wo : @is_well_order cardinal.{u} (<) := ⟨cardinal.wf⟩

/-- The successor cardinal - the smallest cardinal greater than
  `c`. This is not the same as `c + 1` except in the case of finite `c`. -/
def succ (c : cardinal) : cardinal :=
Inf {c' | c < c'}

theorem succ_nonempty (c : cardinal) : {c' : cardinal | c < c'}.nonempty :=
⟨_, cantor _⟩

theorem lt_succ_self (c : cardinal) : c < succ c :=
Inf_mem (succ_nonempty c)

theorem succ_le {a b : cardinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _), λ h, cInf_le' h⟩

@[simp] theorem lt_succ {a b : cardinal} : a < succ b ↔ a ≤ b :=
by rw [← not_le, succ_le, not_lt]

theorem add_one_le_succ (c : cardinal.{u}) : c + 1 ≤ succ c :=
begin
  refine (le_cInf_iff'' (succ_nonempty c)).2 (λ b hlt, _),
  rcases ⟨b, c⟩ with ⟨⟨β⟩, ⟨γ⟩⟩,
  cases le_of_lt hlt with f,
  have : ¬ surjective f := λ hn, (not_le_of_lt hlt) (mk_le_of_surjective hn),
  simp only [surjective, not_forall] at this,
  rcases this with ⟨b, hb⟩,
  calc #γ + 1 = #(option γ) : mk_option.symm
          ... ≤ #β          : (f.option_elim b hb).cardinal_le
end

lemma succ_pos (c : cardinal) : 0 < succ c := by simp

lemma succ_ne_zero (c : cardinal) : succ c ≠ 0 := (succ_pos _).ne'

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → cardinal) : cardinal := mk Σ i, (f i).out

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

@[simp] theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum (λ i, #(f i)) :=
mk_congr $ equiv.sigma_congr_right $ λ i, out_mk_equiv.symm

@[simp] theorem sum_const (ι : Type u) (a : cardinal.{v}) :
  sum (λ i : ι, a) = lift.{v} (#ι) * lift.{u} a :=
induction_on a $ λ α, mk_congr $
  calc (Σ i : ι, quotient.out (#α)) ≃ ι × quotient.out (#α) : equiv.sigma_equiv_prod _ _
  ... ≃ ulift ι × ulift α : equiv.ulift.symm.prod_congr (out_mk_equiv.trans equiv.ulift.symm)

theorem sum_const' (ι : Type u) (a : cardinal.{u}) : sum (λ _:ι, a) = #ι * a := by simp

@[simp] theorem sum_add_distrib {ι} (f g : ι → cardinal) :
  sum (f + g) = sum f + sum g :=
by simpa only [mk_sigma, mk_sum, mk_out, lift_id] using
  mk_congr (equiv.sigma_sum_distrib (quotient.out ∘ f) (quotient.out ∘ g))

@[simp] theorem sum_add_distrib' {ι} (f g : ι → cardinal) :
  cardinal.sum (λ i, f i + g i) = sum f + sum g :=
sum_add_distrib f g

@[simp] theorem lift_sum {ι : Type u} (f : ι → cardinal.{v}) :
  cardinal.lift.{w} (cardinal.sum f) = cardinal.sum (λ i, cardinal.lift.{w} (f i)) :=
equiv.cardinal_eq $ equiv.ulift.trans $ equiv.sigma_congr_right $ λ a, nonempty.some $
  by rw [←lift_mk_eq, mk_out, mk_out, lift_lift]

theorem sum_le_sum {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
⟨(embedding.refl _).sigma_map $ λ i, classical.choice $
  by have := H i; rwa [← quot.out_eq (f i), ← quot.out_eq (g i)] at this⟩

lemma mk_le_mk_mul_of_mk_preimage_le {c : cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
  #α ≤ #β * c :=
by simpa only [←mk_congr (@equiv.sigma_fiber_equiv α β f), mk_sigma, ←sum_const']
  using sum_le_sum _ _ hf

/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bdd_above_range {ι : Type u} (f : ι → cardinal.{max u v}) : bdd_above (set.range f) :=
⟨_, by { rintros a ⟨i, rfl⟩, exact le_sum f i }⟩

instance (a : cardinal.{u}) : small.{u} (set.Iic a) :=
begin
  rw ←mk_out a,
  apply @small_of_surjective (set a.out) (Iic (#a.out)) _ (λ x, ⟨#x, mk_set_le x⟩),
  rintro ⟨x, hx⟩,
  simpa using le_mk_iff_exists_set.1 hx
end

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to an usual ZFC set. -/
theorem bdd_above_iff_small (s : set cardinal.{u}) : bdd_above s ↔ small.{u} s :=
⟨λ ⟨a, ha⟩, @small_subset _ (Iic a) s (λ x h, ha h) _, begin
  rintro ⟨ι, ⟨e⟩⟩,
  suffices : range (λ x : ι, (e.symm x).1) = s,
  { rw ←this,
    apply bdd_above_range.{u u} },
  ext x,
  refine ⟨_, λ hx, ⟨e ⟨x, hx⟩, _⟩⟩,
  { rintro ⟨a, rfl⟩,
    exact (e.symm a).prop },
  { simp_rw [subtype.val_eq_coe, equiv.symm_apply_apply], refl }
end⟩

/-- The indexed supremum of cardinals is the smallest cardinal above
  everything in the family. -/
def sup {ι : Type u} (f : ι → cardinal.{max u v}) : cardinal :=
Sup (set.range f)

theorem le_sup {ι} (f : ι → cardinal.{max u v}) (i) : f i ≤ sup f :=
le_cSup (bdd_above_range f) (mem_range_self i)

theorem sup_le_iff {ι} {f : ι → cardinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
(cSup_le_iff' (bdd_above_range f)).trans (by simp)

theorem sup_le {ι} {f : ι → cardinal} {a} : (∀ i, f i ≤ a) → sup f ≤ a :=
sup_le_iff.2

theorem sup_le_sup {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
sup_le $ λ i, le_trans (H i) (le_sup _ _)

theorem sup_le_sum {ι} (f : ι → cardinal) : sup f ≤ sum f :=
sup_le $ le_sum _

theorem sum_le_sup {ι : Type u} (f : ι → cardinal.{u}) : sum f ≤ #ι * sup.{u u} f :=
by rw ← sum_const'; exact sum_le_sum _ _ (le_sup _)

theorem sum_le_sup_lift {ι : Type u} (f : ι → cardinal.{max u v}) :
  sum f ≤ (#ι).lift * sup.{u v} f :=
begin
  rw [←(sup f).lift_id, ←lift_umax, lift_umax.{(max u v) u}, ←sum_const],
  exact sum_le_sum _ _ (le_sup _)
end

theorem sum_nat_eq_add_sum_succ (f : ℕ → cardinal.{u}) :
  cardinal.sum f = f 0 + cardinal.sum (λ i, f (i + 1)) :=
begin
  refine (equiv.sigma_nat_succ (λ i, quotient.out (f i))).cardinal_eq.trans _,
  simp only [mk_sum, mk_out, lift_id, mk_sigma],
end

theorem sup_eq_zero {ι} {f : ι → cardinal} [is_empty ι] : sup f = 0 :=
by { rw ←nonpos_iff_eq_zero, exact sup_le is_empty_elim }

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → cardinal) : cardinal := #(Π i, (f i).out)

@[simp] theorem mk_pi {ι : Type u} (α : ι → Type v) : #(Π i, α i) = prod (λ i, #(α i)) :=
mk_congr $ equiv.Pi_congr_right $ λ i, out_mk_equiv.symm

@[simp] theorem prod_const (ι : Type u) (a : cardinal.{v}) :
  prod (λ i : ι, a) = lift.{u} a ^ lift.{v} (#ι) :=
induction_on a $ λ α, mk_congr $ equiv.Pi_congr equiv.ulift.symm $
  λ i, out_mk_equiv.trans equiv.ulift.symm

theorem prod_const' (ι : Type u) (a : cardinal.{u}) : prod (λ _:ι, a) = a ^ #ι :=
induction_on a $ λ α, (mk_pi _).symm

theorem prod_le_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
⟨embedding.Pi_congr_right $ λ i, classical.choice $
  by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

@[simp] theorem prod_eq_zero {ι} (f : ι → cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 :=
by { lift f to ι → Type u using λ _, trivial, simp only [mk_eq_zero_iff, ← mk_pi, is_empty_pi] }

theorem prod_ne_zero {ι} (f : ι → cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 :=
by simp [prod_eq_zero]

@[simp] theorem lift_prod {ι : Type u} (c : ι → cardinal.{v}) :
  lift.{w} (prod c) = prod (λ i, lift.{w} (c i)) :=
begin
  lift c to ι → Type v using λ _, trivial,
  simp only [← mk_pi, ← mk_ulift],
  exact mk_congr (equiv.ulift.trans $ equiv.Pi_congr_right $ λ i, equiv.ulift.symm)
end

@[simp] theorem lift_min {ι I} (f : ι → cardinal) :
  lift (cardinal.min I f) = cardinal.min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

theorem lift_down {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a → ∃ a', lift a' = b :=
induction_on₂ a b $ λ α β,
by rw [← lift_id (#β), ← lift_umax, ← lift_umax.{u v}, lift_mk_le]; exact
λ ⟨f⟩, ⟨#(set.range f), eq.symm $ lift_mk_eq.2
  ⟨embedding.equiv_of_surjective
    (embedding.cod_restrict _ f set.mem_range_self)
    $ λ ⟨a, ⟨b, e⟩⟩, ⟨b, subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
le_antisymm
  (le_of_not_gt $ λ h, begin
    rcases lt_lift_iff.1 h with ⟨b, e, h⟩,
    rw [lt_succ, ← lift_le, e] at h,
    exact not_lt_of_le h (lt_succ_self _)
  end)
  (succ_le.2 $ lift_lt.2 $ lt_succ_self _)

@[simp] theorem lift_max {a : cardinal.{u}} {b : cardinal.{v}} :
  lift.{(max v w)} a = lift.{(max u w)} b ↔ lift.{v} a = lift.{u} b :=
calc lift.{(max v w)} a = lift.{(max u w)} b
  ↔ lift.{w} (lift.{v} a) = lift.{w} (lift.{u} b) : by simp
  ... ↔ lift.{v} a = lift.{u} b : lift_inj

@[simp] theorem lift_min' {a b : cardinal} : lift (min a b) = min (lift a) (lift b) :=
begin
  cases le_total a b,
  { rw [min_eq_left h, min_eq_left (lift_le.2 h)] },
  { rw [min_eq_right h, min_eq_right (lift_le.2 h)] }
end

@[simp] theorem lift_max' {a b : cardinal} : lift (max a b) = max (lift a) (lift b) :=
begin
  cases le_total a b,
  { rw [max_eq_right h, max_eq_right (lift_le.2 h)] },
  { rw [max_eq_left h, max_eq_left (lift_le.2 h)] }
end

protected lemma le_sup_iff {ι : Type v} {f : ι → cardinal.{max v w}} {c : cardinal} :
  (c ≤ sup f) ↔ (∀ b, (∀ i, f i ≤ b) → c ≤ b) :=
⟨λ h b hb, le_trans h (sup_le hb), λ h, h _ $ le_sup f⟩

/-- The lift of a supremum is the supremum of the lifts. -/
lemma lift_sup {ι : Type v} (f : ι → cardinal.{max v w}) :
  lift.{u} (sup.{v w} f) = sup.{v (max u w)} (λ i : ι, lift.{u} (f i)) :=
begin
  apply le_antisymm,
  { rw [cardinal.le_sup_iff], intros c hc, by_contra h,
    obtain ⟨d, rfl⟩ := cardinal.lift_down (not_le.mp h).le,
    simp only [lift_le, sup_le_iff] at h hc,
    exact h hc },
  { simp only [cardinal.sup_le, lift_le, le_sup, implies_true_iff] }
end

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
lemma lift_sup_le {ι : Type v} (f : ι → cardinal.{max v w})
  (t : cardinal.{max u v w}) (w : ∀ i, lift.{u} (f i) ≤ t) :
  lift.{u} (sup f) ≤ t :=
by { rw lift_sup, exact sup_le w }

@[simp] lemma lift_sup_le_iff {ι : Type v} (f : ι → cardinal.{max v w}) (t : cardinal.{max u v w}) :
  lift.{u} (sup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t :=
⟨λ h i, (lift_le.mpr (le_sup f i)).trans h,
 λ h, lift_sup_le f t h⟩

universes v' w'

/--
To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
lemma lift_sup_le_lift_sup
  {ι : Type v} {ι' : Type v'} (f : ι → cardinal.{max v w}) (f' : ι' → cardinal.{max v' w'})
  (g : ι → ι') (h : ∀ i, lift.{(max v' w')} (f i) ≤ lift.{(max v w)} (f' (g i))) :
  lift.{(max v' w')} (sup f) ≤ lift.{(max v w)} (sup f') :=
begin
  apply lift_sup_le.{(max v' w')} f,
  intro i,
  apply le_trans (h i),
  simp only [lift_le],
  apply le_sup,
end

/-- A variant of `lift_sup_le_lift_sup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
lemma lift_sup_le_lift_sup'
  {ι : Type v} {ι' : Type v'} (f : ι → cardinal.{v}) (f' : ι' → cardinal.{v'})
  (g : ι → ι') (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) :
  lift.{v'} (sup.{v v} f) ≤ lift.{v} (sup.{v' v'} f') :=
lift_sup_le_lift_sup f f' g h

/-- `ω` is the smallest infinite cardinal, also known as ℵ₀. -/
def omega : cardinal.{u} := lift (#ℕ)

localized "notation `ω` := cardinal.omega" in cardinal

lemma mk_nat : #ℕ = ω := (lift_id _).symm

theorem omega_ne_zero : ω ≠ 0 := mk_ne_zero _

theorem omega_pos : 0 < ω :=
pos_iff_ne_zero.2 omega_ne_zero

@[simp] theorem lift_omega : lift ω = ω := lift_lift _

@[simp] theorem omega_le_lift {c : cardinal.{u}} : ω ≤ lift.{v} c ↔ ω ≤ c :=
by rw [← lift_omega, lift_le]

@[simp] theorem lift_le_omega {c : cardinal.{u}} : lift.{v} c ≤ ω ↔ c ≤ ω :=
by rw [← lift_omega, lift_le]

/-! ### Properties about the cast from `ℕ` -/

@[simp] theorem mk_fin (n : ℕ) : #(fin n) = n := by simp

@[simp] theorem lift_nat_cast (n : ℕ) : lift.{u} (n : cardinal.{v}) = n :=
by induction n; simp *

@[simp] lemma lift_eq_nat_iff {a : cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
lift_injective.eq_iff' (lift_nat_cast n)

@[simp] lemma nat_eq_lift_iff {n : ℕ} {a : cardinal.{u}} :
  (n : cardinal) = lift.{v} a ↔ (n : cardinal) = a :=
by rw [← lift_nat_cast.{v} n, lift_inj]

theorem lift_mk_fin (n : ℕ) : lift (#(fin n)) = n := by simp

lemma mk_finset {α : Type u} {s : finset α} : #s = ↑(finset.card s) := by simp

theorem card_le_of_finset {α} (s : finset α) :
  (s.card : cardinal) ≤ #α :=
begin
  rw (_ : (s.card : cardinal) = #s),
  { exact ⟨function.embedding.subtype _⟩ },
  rw [cardinal.mk_fintype, fintype.card_coe]
end

@[simp, norm_cast] theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : cardinal) = m ^ n :=
by induction n; simp [pow_succ', power_add, *]

@[simp, norm_cast] theorem nat_cast_le {m n : ℕ} : (m : cardinal) ≤ n ↔ m ≤ n :=
by rw [← lift_mk_fin, ← lift_mk_fin, lift_le]; exact
⟨λ ⟨⟨f, hf⟩⟩, by simpa only [fintype.card_fin] using fintype.card_le_of_injective f hf,
  λ h, ⟨(fin.cast_le h).to_embedding⟩⟩

@[simp, norm_cast] theorem nat_cast_lt {m n : ℕ} : (m : cardinal) < n ↔ m < n :=
by simp [lt_iff_le_not_le, -not_le]

instance : char_zero cardinal := ⟨strict_mono.injective $ λ m n, nat_cast_lt.2⟩

theorem nat_cast_inj {m n : ℕ} : (m : cardinal) = n ↔ m = n := nat.cast_inj

lemma nat_cast_injective : injective (coe : ℕ → cardinal) :=
nat.cast_injective

@[simp, norm_cast, priority 900] theorem nat_succ (n : ℕ) : (n.succ : cardinal) = succ n :=
le_antisymm (add_one_le_succ _) (succ_le.2 $ nat_cast_lt.2 $ nat.lt_succ_self _)

@[simp] theorem succ_zero : succ 0 = 1 :=
by norm_cast

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : finset α, s.card ≤ n) :
  # α ≤ n :=
begin
  refine lt_succ.1 (lt_of_not_ge $ λ hn, _),
  rw [← cardinal.nat_succ, ← cardinal.lift_mk_fin n.succ] at hn,
  cases hn with f,
  refine not_lt_of_le (H $ finset.univ.map f) _,
  rw [finset.card_map, ← fintype.card, fintype.card_ulift, fintype.card_fin],
  exact n.lt_succ_self
end

theorem cantor' (a) {b : cardinal} (hb : 1 < b) : a < b ^ a :=
by rw [← succ_le, (by norm_cast : succ 1 = 2)] at hb;
   exact lt_of_lt_of_le (cantor _) (power_le_power_right hb)

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
by rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_omega (n : ℕ) : (n : cardinal.{u}) < ω :=
succ_le.1 $ by rw [← nat_succ, ← lift_mk_fin, omega, lift_mk_le.{0 0 u}]; exact
⟨⟨coe, λ a b, fin.ext⟩⟩

@[simp] theorem one_lt_omega : 1 < ω :=
by simpa using nat_lt_omega 1

theorem lt_omega {c : cardinal.{u}} : c < ω ↔ ∃ n : ℕ, c = n :=
⟨λ h, begin
  rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩,
  rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩,
  suffices : finite S,
  { lift S to finset ℕ using this,
    simp },
  contrapose! h',
  haveI := infinite.to_subtype h',
  exact ⟨infinite.nat_embedding S⟩
end, λ ⟨n, e⟩, e.symm ▸ nat_lt_omega _⟩

theorem omega_le {c : cardinal.{u}} : ω ≤ c ↔ ∀ n : ℕ, (n:cardinal) ≤ c :=
⟨λ h n, le_trans (le_of_lt (nat_lt_omega _)) h,
 λ h, le_of_not_lt $ λ hn, begin
  rcases lt_omega.1 hn with ⟨n, rfl⟩,
  exact not_le_of_lt (nat.lt_succ_self _) (nat_cast_le.1 (h (n+1)))
end⟩

theorem lt_omega_iff_fintype {α : Type u} : #α < ω ↔ nonempty (fintype α) :=
lt_omega.trans ⟨λ ⟨n, e⟩, begin
  rw [← lift_mk_fin n] at e,
  cases quotient.exact e with f,
  exact ⟨fintype.of_equiv _ f.symm⟩
end, λ ⟨_⟩, by exactI ⟨_, mk_fintype _⟩⟩

theorem lt_omega_of_fintype (α : Type u) [fintype α] : #α < ω :=
lt_omega_iff_fintype.2 ⟨infer_instance⟩

theorem lt_omega_iff_finite {α} {S : set α} : #S < ω ↔ finite S :=
lt_omega_iff_fintype.trans finite_def.symm

instance can_lift_cardinal_nat : can_lift cardinal ℕ :=
⟨ coe, λ x, x < ω, λ x hx, let ⟨n, hn⟩ := lt_omega.mp hx in ⟨n, hn.symm⟩⟩

theorem add_lt_omega {a b : cardinal} (ha : a < ω) (hb : b < ω) : a + b < ω :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_omega
end

lemma add_lt_omega_iff {a b : cardinal} : a + b < ω ↔ a < ω ∧ b < ω :=
⟨λ h, ⟨lt_of_le_of_lt (self_le_add_right _ _) h, lt_of_le_of_lt (self_le_add_left _ _) h⟩,
  λ⟨h1, h2⟩, add_lt_omega h1 h2⟩

lemma omega_le_add_iff {a b : cardinal} : ω ≤ a + b ↔ ω ≤ a ∨ ω ≤ b :=
by simp only [← not_lt, add_lt_omega_iff, not_and_distrib]

/-- See also `cardinal.nsmul_lt_omega_iff_of_ne_zero` if you already have `n ≠ 0`. -/
lemma nsmul_lt_omega_iff {n : ℕ} {a : cardinal} : n • a < ω ↔ n = 0 ∨ a < ω :=
begin
  cases n,
  { simpa using nat_lt_omega 0 },
  simp only [nat.succ_ne_zero, false_or],
  induction n with n ih,
  { simp },
  rw [succ_nsmul, add_lt_omega_iff, ih, and_self]
end

/-- See also `cardinal.nsmul_lt_omega_iff` for a hypothesis-free version. -/
lemma nsmul_lt_omega_iff_of_ne_zero {n : ℕ} {a : cardinal} (h : n ≠ 0) : n • a < ω ↔ a < ω :=
nsmul_lt_omega_iff.trans $ or_iff_right h

theorem mul_lt_omega {a b : cardinal} (ha : a < ω) (hb : b < ω) : a * b < ω :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_mul]; apply nat_lt_omega
end

lemma mul_lt_omega_iff {a b : cardinal} : a * b < ω ↔ a = 0 ∨ b = 0 ∨ a < ω ∧ b < ω :=
begin
  split,
  { intro h, by_cases ha : a = 0, { left, exact ha },
    right, by_cases hb : b = 0, { left, exact hb },
    right, rw [← ne, ← one_le_iff_ne_zero] at ha hb, split,
    { rw [← mul_one a],
      refine lt_of_le_of_lt (mul_le_mul' (le_refl a) hb) h },
    { rw [← one_mul b],
      refine lt_of_le_of_lt (mul_le_mul' ha (le_refl b)) h }},
  rintro (rfl|rfl|⟨ha,hb⟩); simp only [*, mul_lt_omega, omega_pos, zero_mul, mul_zero]
end

lemma omega_le_mul_iff {a b : cardinal} : ω ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ω ≤ a ∨ ω ≤ b) :=
let h := (@mul_lt_omega_iff a b).not in
by rwa [not_lt, not_or_distrib, not_or_distrib, not_and_distrib, not_lt, not_lt] at h

lemma mul_lt_omega_iff_of_ne_zero {a b : cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
  a * b < ω ↔ a < ω ∧ b < ω :=
by simp [mul_lt_omega_iff, ha, hb]

theorem power_lt_omega {a b : cardinal} (ha : a < ω) (hb : b < ω) : a ^ b < ω :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_pow]; apply nat_lt_omega
end

lemma eq_one_iff_unique {α : Type*} :
  #α = 1 ↔ subsingleton α ∧ nonempty α :=
calc #α = 1 ↔ #α ≤ 1 ∧ ¬#α < 1 : eq_iff_le_not_lt
        ... ↔ subsingleton α ∧ nonempty α :
begin
  apply and_congr le_one_iff_subsingleton,
  push_neg,
  rw [one_le_iff_ne_zero, mk_ne_zero_iff]
end

theorem infinite_iff {α : Type u} : infinite α ↔ ω ≤ #α :=
by rw [←not_lt, lt_omega_iff_fintype, not_nonempty_iff, is_empty_fintype]

@[simp] lemma omega_le_mk (α : Type u) [infinite α] : ω ≤ #α := infinite_iff.1 ‹_›

lemma encodable_iff {α : Type u} : nonempty (encodable α) ↔ #α ≤ ω :=
⟨λ ⟨h⟩, ⟨(@encodable.encode' α h).trans equiv.ulift.symm.to_embedding⟩,
  λ ⟨h⟩, ⟨encodable.of_inj _ (h.trans equiv.ulift.to_embedding).injective⟩⟩

@[simp] lemma mk_le_omega [encodable α] : #α ≤ ω := encodable_iff.1 ⟨‹_›⟩

lemma denumerable_iff {α : Type u} : nonempty (denumerable α) ↔ #α = ω :=
⟨λ ⟨h⟩, mk_congr ((@denumerable.eqv α h).trans equiv.ulift.symm),
 λ h, by { cases quotient.exact h with f, exact ⟨denumerable.mk' $ f.trans equiv.ulift⟩ }⟩

@[simp] lemma mk_denumerable (α : Type u) [denumerable α] : #α = ω :=
denumerable_iff.1 ⟨‹_›⟩

@[simp] lemma mk_set_le_omega (s : set α) : #s ≤ ω ↔ countable s :=
begin
  rw [countable_iff_exists_injective], split,
  { rintro ⟨f'⟩, cases embedding.trans f' equiv.ulift.to_embedding with f hf, exact ⟨f, hf⟩ },
  { rintro ⟨f, hf⟩, exact ⟨embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding⟩ }
end

@[simp] lemma omega_add_omega : ω + ω = ω := mk_denumerable _

lemma omega_mul_omega : ω * ω = ω := mk_denumerable _

@[simp] lemma add_le_omega {c₁ c₂ : cardinal} : c₁ + c₂ ≤ ω ↔ c₁ ≤ ω ∧ c₂ ≤ ω :=
⟨λ h, ⟨le_self_add.trans h, le_add_self.trans h⟩, λ h, omega_add_omega ▸ add_le_add h.1 h.2⟩

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
def to_nat : zero_hom cardinal ℕ :=
⟨λ c, if h : c < omega.{v} then classical.some (lt_omega.1 h) else 0,
  begin
    have h : 0 < ω := nat_lt_omega 0,
    rw [dif_pos h, ← cardinal.nat_cast_inj, ← classical.some_spec (lt_omega.1 h), nat.cast_zero],
  end⟩

lemma to_nat_apply_of_lt_omega {c : cardinal} (h : c < ω) :
  c.to_nat = classical.some (lt_omega.1 h) :=
dif_pos h

@[simp]
lemma to_nat_apply_of_omega_le {c : cardinal} (h : ω ≤ c) :
  c.to_nat = 0 :=
dif_neg (not_lt_of_le h)

@[simp]
lemma cast_to_nat_of_lt_omega {c : cardinal} (h : c < ω) :
  ↑c.to_nat = c :=
by rw [to_nat_apply_of_lt_omega h, ← classical.some_spec (lt_omega.1 h)]

@[simp]
lemma cast_to_nat_of_omega_le {c : cardinal} (h : ω ≤ c) :
  ↑c.to_nat = (0 : cardinal) :=
by rw [to_nat_apply_of_omega_le h, nat.cast_zero]

lemma to_nat_le_iff_le_of_lt_omega {c d : cardinal} (hc : c < ω) (hd : d < ω) :
  c.to_nat ≤ d.to_nat ↔ c ≤ d :=
by rw [←nat_cast_le, cast_to_nat_of_lt_omega hc, cast_to_nat_of_lt_omega hd]

lemma to_nat_lt_iff_lt_of_lt_omega {c d : cardinal} (hc : c < ω) (hd : d < ω) :
  c.to_nat < d.to_nat ↔ c < d :=
by rw [←nat_cast_lt, cast_to_nat_of_lt_omega hc, cast_to_nat_of_lt_omega hd]

lemma to_nat_le_of_le_of_lt_omega {c d : cardinal} (hd : d < ω) (hcd : c ≤ d) :
  c.to_nat ≤ d.to_nat :=
(to_nat_le_iff_le_of_lt_omega (lt_of_le_of_lt hcd hd) hd).mpr hcd

lemma to_nat_lt_of_lt_of_lt_omega {c d : cardinal} (hd : d < ω) (hcd : c < d) :
  c.to_nat < d.to_nat :=
(to_nat_lt_iff_lt_of_lt_omega (hcd.trans hd) hd).mpr hcd

@[simp]
lemma to_nat_cast (n : ℕ) : cardinal.to_nat n = n :=
begin
  rw [to_nat_apply_of_lt_omega (nat_lt_omega n), ← nat_cast_inj],
  exact (classical.some_spec (lt_omega.1 (nat_lt_omega n))).symm,
end

/-- `to_nat` has a right-inverse: coercion. -/
lemma to_nat_right_inverse : function.right_inverse (coe : ℕ → cardinal) to_nat := to_nat_cast

lemma to_nat_surjective : surjective to_nat := to_nat_right_inverse.surjective

@[simp]
lemma mk_to_nat_of_infinite [h : infinite α] : (#α).to_nat = 0 :=
dif_neg (not_lt_of_le (infinite_iff.1 h))

lemma mk_to_nat_eq_card [fintype α] : (#α).to_nat = fintype.card α := by simp

@[simp]
lemma zero_to_nat : to_nat 0 = 0 :=
by rw [← to_nat_cast 0, nat.cast_zero]

@[simp]
lemma one_to_nat : to_nat 1 = 1 :=
by rw [← to_nat_cast 1, nat.cast_one]

@[simp] lemma to_nat_eq_one {c : cardinal} : to_nat c = 1 ↔ c = 1 :=
⟨λ h, (cast_to_nat_of_lt_omega (lt_of_not_ge (one_ne_zero ∘ h.symm.trans ∘
  to_nat_apply_of_omega_le))).symm.trans ((congr_arg coe h).trans nat.cast_one),
  λ h, (congr_arg to_nat h).trans one_to_nat⟩

lemma to_nat_eq_one_iff_unique {α : Type*} : (#α).to_nat = 1 ↔ subsingleton α ∧ nonempty α :=
to_nat_eq_one.trans eq_one_iff_unique

@[simp] lemma to_nat_lift (c : cardinal.{v}) : (lift.{u v} c).to_nat = c.to_nat :=
begin
  apply nat_cast_injective,
  cases lt_or_ge c ω with hc hc,
  { rw [cast_to_nat_of_lt_omega, ←lift_nat_cast, cast_to_nat_of_lt_omega hc],
    rwa [←lift_omega, lift_lt] },
  { rw [cast_to_nat_of_omega_le, ←lift_nat_cast, cast_to_nat_of_omega_le hc, lift_zero],
    rwa [←lift_omega, lift_le] },
end

lemma to_nat_congr {β : Type v} (e : α ≃ β) : (#α).to_nat = (#β).to_nat :=
by rw [←to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]

@[simp] lemma to_nat_mul (x y : cardinal) : (x * y).to_nat = x.to_nat * y.to_nat :=
begin
  by_cases hx1 : x = 0,
  { rw [comm_semiring.mul_comm, hx1, mul_zero, zero_to_nat, nat.zero_mul] },
  by_cases hy1 : y = 0,
  { rw [hy1, zero_to_nat, mul_zero, mul_zero, zero_to_nat] },
  refine nat_cast_injective (eq.trans _ (nat.cast_mul _ _).symm),
  cases lt_or_ge x ω with hx2 hx2,
  { cases lt_or_ge y ω with hy2 hy2,
    { rw [cast_to_nat_of_lt_omega, cast_to_nat_of_lt_omega hx2, cast_to_nat_of_lt_omega hy2],
      exact mul_lt_omega hx2 hy2 },
    { rw [cast_to_nat_of_omega_le hy2, mul_zero, cast_to_nat_of_omega_le],
      exact not_lt.mp (mt (mul_lt_omega_iff_of_ne_zero hx1 hy1).mp (λ h, not_lt.mpr hy2 h.2)) } },
  { rw [cast_to_nat_of_omega_le hx2, zero_mul, cast_to_nat_of_omega_le],
    exact not_lt.mp (mt (mul_lt_omega_iff_of_ne_zero hx1 hy1).mp (λ h, not_lt.mpr hx2 h.1)) },
end

@[simp] lemma to_nat_add_of_lt_omega {a : cardinal.{u}} {b : cardinal.{v}}
  (ha : a < ω) (hb : b < ω) : ((lift.{v u} a) + (lift.{u v} b)).to_nat = a.to_nat + b.to_nat :=
begin
  apply cardinal.nat_cast_injective,
  replace ha : (lift.{v u} a) < ω := by { rw [← lift_omega], exact lift_lt.2 ha },
  replace hb : (lift.{u v} b) < ω := by { rw [← lift_omega], exact lift_lt.2 hb },
  rw [nat.cast_add, ← to_nat_lift.{v u} a, ← to_nat_lift.{u v} b, cast_to_nat_of_lt_omega ha,
    cast_to_nat_of_lt_omega hb, cast_to_nat_of_lt_omega (add_lt_omega ha hb)]
end

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
def to_enat : cardinal →+ enat :=
{ to_fun := λ c, if c < omega.{v} then c.to_nat else ⊤,
  map_zero' := by simp [if_pos (lt_trans zero_lt_one one_lt_omega)],
  map_add' := λ x y, begin
    by_cases hx : x < ω,
    { obtain ⟨x0, rfl⟩ := lt_omega.1 hx,
      by_cases hy : y < ω,
      { obtain ⟨y0, rfl⟩ := lt_omega.1 hy,
        simp only [add_lt_omega hx hy, hx, hy, to_nat_cast, if_true],
        rw [← nat.cast_add, to_nat_cast, nat.cast_add] },
      { rw [if_neg hy, if_neg, enat.add_top],
        contrapose! hy,
        apply lt_of_le_of_lt le_add_self hy } },
    { rw [if_neg hx, if_neg, enat.top_add],
      contrapose! hx,
      apply lt_of_le_of_lt le_self_add hx },
  end }

@[simp]
lemma to_enat_apply_of_lt_omega {c : cardinal} (h : c < ω) :
  c.to_enat = c.to_nat :=
if_pos h

@[simp]
lemma to_enat_apply_of_omega_le {c : cardinal} (h : ω ≤ c) :
  c.to_enat = ⊤ :=
if_neg (not_lt_of_le h)

@[simp]
lemma to_enat_cast (n : ℕ) : cardinal.to_enat n = n :=
by rw [to_enat_apply_of_lt_omega (nat_lt_omega n), to_nat_cast]

@[simp]
lemma mk_to_enat_of_infinite [h : infinite α] : (#α).to_enat = ⊤ :=
to_enat_apply_of_omega_le (infinite_iff.1 h)

lemma to_enat_surjective : surjective to_enat :=
begin
  intro x,
  exact enat.cases_on x ⟨ω, to_enat_apply_of_omega_le (le_refl ω)⟩
    (λ n, ⟨n, to_enat_cast n⟩),
end

lemma mk_to_enat_eq_coe_card [fintype α] : (#α).to_enat = fintype.card α :=
by simp

lemma mk_int : #ℤ = ω := mk_denumerable ℤ

lemma mk_pnat : #ℕ+ = ω := mk_denumerable ℕ+

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
lt_of_not_ge $ λ ⟨F⟩, begin
  haveI : inhabited (Π (i : ι), (g i).out),
  { refine ⟨λ i, classical.choice $ mk_ne_zero_iff.1 _⟩,
    rw mk_out,
    exact (H i).ne_bot },
  let G := inv_fun F,
  have sG : surjective G := inv_fun_surjective F.2,
  choose C hc using show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b,
  { assume i,
    simp only [- not_exists, not_exists.symm, not_forall.symm],
    refine λ h, not_le_of_lt (H i) _,
    rw [← mk_out (f i), ← mk_out (g i)],
    exact ⟨embedding.of_surjective _ h⟩ },
  exact (let ⟨⟨i, a⟩, h⟩ := sG C in hc i a (congr_fun h _))
end

@[simp] theorem mk_empty : #empty = 0 := mk_eq_zero _

@[simp] theorem mk_pempty : #pempty = 0 := mk_eq_zero _

@[simp] theorem mk_punit : #punit = 1 := mk_eq_one punit

theorem mk_unit : #unit = 1 := mk_punit

@[simp] theorem mk_singleton {α : Type u} (x : α) : #({x} : set α) = 1 :=
mk_eq_one _

@[simp] theorem mk_plift_true : #(plift true) = 1 := mk_eq_one _
@[simp] theorem mk_plift_false : #(plift false) = 0 := mk_eq_zero _

@[simp] theorem mk_vector (α : Type u) (n : ℕ) : #(vector α n) = (#α) ^ℕ n :=
(mk_congr (equiv.vector_equiv_fin α n)).trans $ by simp

theorem mk_list_eq_sum_pow (α : Type u) : #(list α) = sum (λ n : ℕ, (#α) ^ℕ n) :=
calc #(list α) = #(Σ n, vector α n) : mk_congr (equiv.sigma_fiber_equiv list.length).symm
... = sum (λ n : ℕ, (#α) ^ℕ n) : by simp

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(quot r) ≤ #α :=
mk_le_of_surjective quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : setoid α} : #(quotient s) ≤ #α :=
mk_quot_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
  #(subtype p) ≤ #(subtype q) :=
⟨embedding.subtype_map (embedding.refl α) h⟩

@[simp] theorem mk_emptyc (α : Type u) : #(∅ : set α) = 0 := mk_eq_zero _

lemma mk_emptyc_iff {α : Type u} {s : set α} : #s = 0 ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw mk_eq_zero_iff at h,
    exact eq_empty_iff_forall_not_mem.2 (λ x hx, h.elim' ⟨x, hx⟩) },
  { rintro rfl, exact mk_emptyc _ }
end

@[simp] theorem mk_univ {α : Type u} : #(@univ α) = #α :=
mk_congr (equiv.set.univ α)

theorem mk_image_le {α β : Type u} {f : α → β} {s : set α} : #(f '' s) ≤ #s :=
mk_le_of_surjective surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : set α} :
  lift.{u} (#(f '' s)) ≤ lift.{v} (#s) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α :=
mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
  lift.{u} (#(range f)) ≤ lift.{v} (#α) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_range⟩

lemma mk_range_eq (f : α → β) (h : injective f) : #(range f) = #α :=
mk_congr ((equiv.of_injective f h).symm)

lemma mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{u} (#(range f)) = lift.{v} (#α) :=
lift_mk_eq'.mpr ⟨(equiv.of_injective f hf).symm⟩

lemma mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{(max u w)} (# (range f)) = lift.{(max v w)} (# α) :=
lift_mk_eq.mpr ⟨(equiv.of_injective f hf).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : set α} (hf : injective f) :
  #(f '' s) = #s :=
mk_congr ((equiv.set.image f s hf).symm)

theorem mk_Union_le_sum_mk {α ι : Type u} {f : ι → set α} : #(⋃ i, f i) ≤ sum (λ i, #(f i)) :=
calc #(⋃ i, f i) ≤ #(Σ i, f i)        : mk_le_of_surjective (set.sigma_to_Union_surjective f)
              ... = sum (λ i, #(f i)) : mk_sigma _

theorem mk_Union_eq_sum_mk {α ι : Type u} {f : ι → set α} (h : ∀i j, i ≠ j → disjoint (f i) (f j)) :
  #(⋃ i, f i) = sum (λ i, #(f i)) :=
calc #(⋃ i, f i) = #(Σ i, f i)       : mk_congr (set.Union_eq_sigma_of_disjoint h)
              ... = sum (λi, #(f i)) : mk_sigma _

lemma mk_Union_le {α ι : Type u} (f : ι → set α) :
  #(⋃ i, f i) ≤ #ι * cardinal.sup.{u u} (λ i, #(f i)) :=
le_trans mk_Union_le_sum_mk (sum_le_sup _)

lemma mk_sUnion_le {α : Type u} (A : set (set α)) :
  #(⋃₀ A) ≤ #A * cardinal.sup.{u u} (λ s : A, #s) :=
by { rw [sUnion_eq_Union], apply mk_Union_le }

lemma mk_bUnion_le {ι α : Type u} (A : ι → set α) (s : set ι) :
  #(⋃(x ∈ s), A x) ≤ #s * cardinal.sup.{u u} (λ x : s, #(A x.1)) :=
by { rw [bUnion_eq_Union], apply mk_Union_le }

lemma finset_card_lt_omega (s : finset α) : #(↑s : set α) < ω :=
by { rw [lt_omega_iff_fintype], exact ⟨finset.subtype.fintype s⟩ }

theorem mk_eq_nat_iff_finset {α} {s : set α} {n : ℕ} :
  #s = n ↔ ∃ t : finset α, (t : set α) = s ∧ t.card = n :=
begin
  split,
  { intro h,
    lift s to finset α using lt_omega_iff_finite.1 (h.symm ▸ nat_lt_omega n),
    simpa using h },
  { rintro ⟨t, rfl, rfl⟩,
    exact mk_finset }
end

theorem mk_union_add_mk_inter {α : Type u} {S T : set α} :
  #(S ∪ T : set α) + #(S ∩ T : set α) = #S + #T :=
quot.sound ⟨equiv.set.union_sum_inter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
lemma mk_union_le {α : Type u} (S T : set α) : #(S ∪ T : set α) ≤ #S + #T :=
@mk_union_add_mk_inter α S T ▸ self_le_add_right (#(S ∪ T : set α)) (#(S ∩ T : set α))

theorem mk_union_of_disjoint {α : Type u} {S T : set α} (H : disjoint S T) :
  #(S ∪ T : set α) = #S + #T :=
quot.sound ⟨equiv.set.union H⟩

theorem mk_insert {α : Type u} {s : set α} {a : α} (h : a ∉ s) :
  #(insert a s : set α) = #s + 1 :=
by { rw [← union_singleton, mk_union_of_disjoint, mk_singleton], simpa }

lemma mk_sum_compl {α} (s : set α) : #s + #(sᶜ : set α) = #α :=
mk_congr (equiv.set.sum_compl s)

lemma mk_le_mk_of_subset {α} {s t : set α} (h : s ⊆ t) : #s ≤ #t :=
⟨set.embedding_of_subset s t h⟩

lemma mk_subtype_mono {p q : α → Prop} (h : ∀x, p x → q x) : #{x // p x} ≤ #{x // q x} :=
⟨embedding_of_subset _ _ h⟩

lemma mk_union_le_omega {α} {P Q : set α} : #((P ∪ Q : set α)) ≤ ω ↔ #P ≤ ω ∧ #Q ≤ ω :=
by simp

lemma mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : set α) (h : injective f) :
  lift.{u} (#(f '' s)) = lift.{v} (#s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image f s h).symm⟩

lemma mk_image_eq_of_inj_on_lift {α : Type u} {β : Type v} (f : α → β) (s : set α)
  (h : inj_on f s) : lift.{u} (#(f '' s)) = lift.{v} (#s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image_of_inj_on f s h).symm⟩

lemma mk_image_eq_of_inj_on {α β : Type u} (f : α → β) (s : set α) (h : inj_on f s) :
  #(f '' s) = #s :=
mk_congr ((equiv.set.image_of_inj_on f s h).symm)

lemma mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
  #{a : α // p (e a)} = #{b : β // p b} :=
mk_congr (equiv.subtype_equiv_of_subtype e)

lemma mk_sep (s : set α) (t : α → Prop) : #({ x ∈ s | t x } : set α) = #{ x : s | t x.1 } :=
mk_congr (equiv.set.sep s t)

lemma mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) : lift.{v} (#(f ⁻¹' s)) ≤ lift.{u} (#s) :=
begin
  rw lift_mk_le.{u v 0}, use subtype.coind (λ x, f x.1) (λ x, x.2),
  apply subtype.coind_injective, exact h.comp subtype.val_injective
end

lemma mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : s ⊆ range f) : lift.{u} (#s) ≤ lift.{v} (#(f ⁻¹' s)) :=
begin
  rw lift_mk_le.{v u 0},
  refine ⟨⟨_, _⟩⟩,
  { rintro ⟨y, hy⟩, rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩, exact ⟨x, hy⟩ },
  rintro ⟨y, hy⟩ ⟨y', hy'⟩, dsimp,
  rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩,
  rcases classical.subtype_of_exists (h hy') with ⟨x', rfl⟩,
  simp, intro hxx', rw hxx'
end

lemma mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : lift.{v} (#(f ⁻¹' s)) = lift.{u} (#s) :=
le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

lemma mk_preimage_of_injective (f : α → β) (s : set β) (h : injective f) :
  #(f ⁻¹' s) ≤ #s :=
by { convert mk_preimage_of_injective_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_subset_range (f : α → β) (s : set β)
  (h : s ⊆ range f) : #s ≤ #(f ⁻¹' s) :=
by { convert mk_preimage_of_subset_range_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_injective_of_subset_range (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s :=
by { convert mk_preimage_of_injective_of_subset_range_lift.{u u} f s h h2 using 1; rw [lift_id] }

lemma mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : set α}
  {t : set β} (h : t ⊆ f '' s) :
    lift.{u} (#t) ≤ lift.{v} (#({ x ∈ s | f x ∈ t } : set α)) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range_lift _ _ h using 1,
     rw [mk_sep], refl }

lemma mk_subset_ge_of_subset_image (f : α → β) {s : set α} {t : set β} (h : t ⊆ f '' s) :
  #t ≤ #({ x ∈ s | f x ∈ t } : set α) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range _ _ h using 1,
     rw [mk_sep], refl }

theorem le_mk_iff_exists_subset {c : cardinal} {α : Type u} {s : set α} :
  c ≤ #s ↔ ∃ p : set α, p ⊆ s ∧ #p = c :=
begin
  rw [le_mk_iff_exists_set, ←subtype.exists_set_subtype],
  apply exists_congr, intro t, rw [mk_image_eq], apply subtype.val_injective
end

lemma two_le_iff : (2 : cardinal) ≤ #α ↔ ∃x y : α, x ≠ y :=
begin
  split,
  { rintro ⟨f⟩, refine ⟨f $ sum.inl ⟨⟩, f $ sum.inr ⟨⟩, _⟩, intro h, cases f.2 h },
  { rintro ⟨x, y, h⟩, by_contra h',
    rw [not_le, ←nat.cast_two, nat_succ, lt_succ, nat.cast_one, le_one_iff_subsingleton] at h',
    apply h, exactI subsingleton.elim _ _ }
end

lemma two_le_iff' (x : α) : (2 : cardinal) ≤ #α ↔ ∃y : α, x ≠ y :=
begin
  rw [two_le_iff],
  split,
  { rintro ⟨y, z, h⟩, refine classical.by_cases (λ(h' : x = y), _) (λ h', ⟨y, h'⟩),
    rw [←h'] at h, exact ⟨z, h⟩ },
  { rintro ⟨y, h⟩, exact ⟨x, y, h⟩ }
end

lemma exists_not_mem_of_length_le {α : Type*} (l : list α) (h : ↑l.length < # α) :
  ∃ (z : α), z ∉ l :=
begin
  contrapose! h,
  calc # α = # (set.univ : set α) : mk_univ.symm
    ... ≤ # l.to_finset           : mk_le_mk_of_subset (λ x _, list.mem_to_finset.mpr (h x))
    ... = l.to_finset.card        : cardinal.mk_finset
    ... ≤ l.length                : cardinal.nat_cast_le.mpr (list.to_finset_card_le l),
end

lemma three_le {α : Type*} (h : 3 ≤ # α) (x : α) (y : α) :
  ∃ (z : α), z ≠ x ∧ z ≠ y :=
begin
  have : ((3:nat) : cardinal) ≤ # α, simpa using h,
  have : ((2:nat) : cardinal) < # α, rwa [← cardinal.succ_le, ← cardinal.nat_succ],
  have := exists_not_mem_of_length_le [x, y] this,
  simpa [not_or_distrib] using this,
end

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ.
  We index over {s : set β.out // #s < β } instead of {γ // γ < β}, because the latter lives in a
  higher universe -/
def powerlt (α β : cardinal.{u}) : cardinal.{u} :=
sup.{u u} (λ(s : {s : set β.out // #s < β}), α ^ mk.{u} s)

infix ` ^< `:80 := powerlt

theorem powerlt_aux {c c' : cardinal} (h : c < c') :
  ∃(s : {s : set c'.out // #s < c'}), #s = c :=
begin
  cases out_embedding.mp (le_of_lt h) with f,
  have : #↥(range ⇑f) = c, { rwa [mk_range_eq, mk, quotient.out_eq c], exact f.2 },
  exact ⟨⟨range f, by convert h⟩, this⟩
end

lemma le_powerlt {c₁ c₂ c₃ : cardinal} (h : c₂ < c₃) : c₁ ^ c₂ ≤ c₁ ^< c₃ :=
by { rcases powerlt_aux h with ⟨s, rfl⟩, apply le_sup _ s }

lemma powerlt_le {c₁ c₂ c₃ : cardinal} : c₁ ^< c₂ ≤ c₃ ↔ ∀(c₄ < c₂), c₁ ^ c₄ ≤ c₃ :=
begin
  rw [powerlt, sup_le_iff],
  split,
  { intros h c₄ hc₄, rcases powerlt_aux hc₄ with ⟨s, rfl⟩, exact h s },
  intros h s, exact h _ s.2
end

lemma powerlt_le_powerlt_left {a b c : cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
by { rw [powerlt, sup_le_iff], exact λ ⟨s, hs⟩, le_powerlt (lt_of_lt_of_le hs h) }

lemma powerlt_succ {c₁ c₂ : cardinal} (h : c₁ ≠ 0) : c₁ ^< c₂.succ = c₁ ^ c₂ :=
begin
  apply le_antisymm,
  { rw powerlt_le, intros c₃ h2, apply power_le_power_left h, rwa [←lt_succ] },
  { apply le_powerlt, apply lt_succ_self }
end

lemma powerlt_max {c₁ c₂ c₃ : cardinal} : c₁ ^< max c₂ c₃ = max (c₁ ^< c₂) (c₁ ^< c₃) :=
by { cases le_total c₂ c₃; simp only [max_eq_left, max_eq_right, h, powerlt_le_powerlt_left] }

lemma zero_powerlt {a : cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intros c hc, apply zero_power_le },
  convert le_powerlt (pos_iff_ne_zero.2 h), rw [power_zero]
end

lemma powerlt_zero {a : cardinal} : a ^< 0 = 0 :=
begin
  convert sup_eq_zero,
  exact subtype.is_empty_of_false (λ x, (zero_le _).not_lt),
end

end cardinal
