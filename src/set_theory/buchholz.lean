/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import set_theory.cardinal_ordinal

/-!
# Buchholz's psi functions

Buchholz's psi functions are a fast-growing family of ordinal functions. Intuitively speaking,
`buchholz a v` is the least ordinal that can't be made with reference to `buchholz o v` for `o < a`,
and `Omega v`. Here, `Omega v` is defined so that `Omega 0 = 1` and `Omega v = aleph v` otherwise.

More explicitly, we define an inductive type `buchholz_exp' o v` of "Buchholz expressions",
containing an expression for all ordinals up to `Omega v`, and closed under sums and applications of
a function `Ψ u` for `u : ℕ`. Any such expression can be evaluated by plugging in a family of
functions `Ψ`. We then define the type of well-formed Buchholz expressions `buchholz_exp' o v Ψ`
with respect to `Ψ` as those expressions where `Ψ` is only evaluated at values less than `o`.
Finally, we define `buchholz o v` as the least ordinal that isn't the value of some well-formed
Buchholz expression with respect to the Buchholz functions at lesser values.

## Main definitions

- `buchholz_exp'`: the type of Buchholz expressions.
- `buchholz_exp`: the type of well-formed Buchholz expressions.
- `buchholz`: the Buchholz psi functions.

## Implementation details

Buchholz originally defined his psi functions up to `Ψ ω`. However, for the sake of simplicity, we
build them only for natural indices. In truth, one could index them by any countable ordinal, and
many of the results would remain true.

## Todo

Prove all the theorems in Section 1 of Buchholz's paper.

## References:

- [W. Buchholz, A New System of Proof-Theoretic Ordinal Functions][buchholz1986]
-/

noncomputable theory

universes u v

open cardinal
open_locale cardinal

namespace ordinal

/-- The `Ωᵥ` function as defined by Buchholz. This is such that `Omega 0 = 1` and
`Omega v = aleph v` otherwise. -/
def Omega : ℕ → cardinal.{0}
| 0       := 1
| (v + 1) := aleph (v + 1)

theorem Omega_zero : Omega 0 = 1 :=
rfl

theorem Omega_pos : Π v, 0 < Omega v
| 0       := cardinal.zero_lt_one
| (v + 1) := aleph_pos _

theorem Omega_eq_aleph : Π v : ℕ, 0 < v → Omega v = aleph v
| 0       := λ h, h.false.elim
| (v + 1) := λ _, rfl

theorem Omega_le_aleph : Π v, Omega v ≤ aleph v
| 0       := by { convert le_of_lt cardinal.one_lt_omega, exact aleph_zero }
| (v + 1) := rfl.le

theorem Omega_strict_mono : strict_mono Omega :=
begin
  rintros ⟨_⟩ ⟨_⟩ h,
  { exact (lt_irrefl 0 h).elim },
  { exact cardinal.one_lt_omega.trans_le (omega_le_aleph b.succ) },
  { exact (not_lt_bot h).elim },
  { exact cardinal.aleph_lt.2 (ordinal.nat_cast_lt.2 h) }
end

theorem principal_add_Omega : Π v : ℕ, principal (+) (Omega v).ord
| 0 := by { rw [Omega_zero, ord_one], exact principal_add_one }
| (v + 1) := principal_add_aleph _

/-- The type of all Buchholz expressions. These may consist of
* ordinals less than `Ωᵥ`
* sums of two other Buchholz expressions
* some function `Ψᵤ` applied to a Buchholz expression

For the type of well-founded expressions, see `buchholz_exp`. -/
inductive buchholz_exp' (v : ℕ) : Type 0
| lt_Omega' (a : (Omega v).ord.out.α) : buchholz_exp'
| add       (a b : buchholz_exp') : buchholz_exp'
| psi       (u : ℕ) (a : buchholz_exp') : buchholz_exp'

instance (v : ℕ) : has_add (buchholz_exp' v) :=
⟨buchholz_exp'.add⟩

namespace buchholz_exp'

/-- A Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord) : buchholz_exp' v :=
buchholz_exp'.lt_Omega' (enum (<) a (by rwa type_lt))

instance (v : ℕ) : has_zero (buchholz_exp' v) :=
⟨lt_Omega (ord_lt_ord.2 (Omega_pos v))⟩

instance (v : ℕ) : inhabited (buchholz_exp' v) :=
⟨0⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
noncomputable def value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  buchholz_exp' v → ordinal
| (lt_Omega' a)  := typein (<) a
| (a + b)        := a.value + b.value
| (psi u a)      := if ha : a.value < o then Ψ _ ha u else 0

@[simp] theorem lt_Omega'_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : (lt_Omega' a).value Ψ = typein (<) a :=
rfl

@[simp] theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha).value Ψ = a :=
typein_enum _ _

@[simp] theorem zero_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  (0 : buchholz_exp' v).value Ψ = 0 :=
by { convert lt_Omega'_value _ _, simp }

theorem value_zero {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  Π (e : buchholz_exp' v), e.value Ψ < (Omega v).ord
| (lt_Omega' a)  := typein_lt_self _
| (a + b)        := by { unfold value, apply principal_add_Omega; apply value_zero }
| (psi u a)      := begin
  unfold value,
  split_ifs,
  { simp_rw ho at h,
    exact (not_lt_bot h).elim },
  { rw ←ord_zero,
    exact ord_lt_ord.2 (Omega_pos v) }
end

@[simp] theorem add_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e₁ e₂ : buchholz_exp' v) : (e₁ + e₂).value Ψ = e₁.value Ψ + e₂.value Ψ :=
by unfold value

@[simp] theorem add_value' {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e₁ e₂ : buchholz_exp' v) : (add e₁ e₂).value Ψ = e₁.value Ψ + e₂.value Ψ :=
add_value Ψ e₁ e₂

@[simp] theorem psi_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (u : ℕ) {e : buchholz_exp' v} (he : e.value Ψ < o) : (psi u e).value Ψ = Ψ (e.value Ψ) he u :=
by { unfold value, exact dif_pos he }

/-- The height of a Buchholz expression, as a syntax tree. -/
noncomputable def height {v : ℕ} : buchholz_exp' v → ℕ
| (lt_Omega' a) := 0
| (a + b)       := max (height a) (height b) + 1
| (psi u a)     := height a + 1

@[simp] theorem lt_Omega'_height {v : ℕ} (a) : height (@lt_Omega' v a) = 0 :=
rfl

theorem lt_Omega'_of_height {v : ℕ} {e : buchholz_exp' v} (he : height e = 0) :
  ∃ a, e = lt_Omega' a :=
by { induction e with a, use a, all_goals { simpa only [height] } }

theorem left_height_lt_add_height {v : ℕ} (a b : buchholz_exp' v) : a.height < (a + b).height :=
by { unfold height, exact nat.lt_succ_iff.2 (le_max_left _ _) }

theorem right_height_lt_add_height {v : ℕ} (a b : buchholz_exp' v) : b.height < (a + b).height :=
by { unfold height, exact nat.lt_succ_iff.2 (le_max_right _ _) }

@[simp] theorem psi_height {v : ℕ} (u : ℕ) (a : buchholz_exp' v) :
  (psi u a).height = a.height + 1 :=
by unfold height

/-- An auxiliary definition which gives a denumerable family of well-formed Buchholz expressions. -/
def add_iterate (n : ℕ) : buchholz_exp' 0 :=
((+) 0)^[n] 0

theorem add_iterate_succ (n : ℕ) : add_iterate n.succ = 0 + (((+) 0)^[n] 0) :=
function.iterate_succ_apply' _ _ _

theorem add_iterate.inj : function.injective add_iterate :=
begin
  intros m n h,
  induction m with m hm generalizing n; cases n,
  all_goals { simp only [add_iterate, function.iterate_succ'] at h },
  any_goals { cases h },
  rw hm (add.inj h).right
end

private theorem mk_height_le_aleph (v : ℕ) : Π h, # {e : buchholz_exp' v | e.height ≤ h} ≤ aleph v
| 0 := begin
  refine le_trans _ (Omega_le_aleph v),
  let f : ↥{e : buchholz_exp' v | e.height = 0} → (Omega v).ord.out.α :=
    λ e, classical.some (lt_Omega'_of_height e.prop),
  have hf : function.injective f := begin
    intros e₁ e₂ h,
    apply_fun lt_Omega' at h,
    have H := λ e : ↥{e : buchholz_exp' v | e.height = 0},
      classical.some_spec (lt_Omega'_of_height e.prop),
    rwa [←H, ←H, ←subtype.ext_iff] at h
  end,
  convert mk_le_of_injective hf,
  simp only [nonpos_iff_eq_zero],
  exact (mk_ord_out _).symm
end
| (h + 1) := begin
  let α : Type := {e : buchholz_exp' v | e.height ≤ h},
  have hα : mk α ≤ aleph v := mk_height_le_aleph h,
  let f : ↥{e : buchholz_exp' v | e.height ≤ h + 1} → (Omega v).ord.out.α ⊕ (α × α) ⊕ (ℕ × α) :=
  begin
    rintro ⟨a | ⟨a, b⟩ | ⟨u, a⟩, he⟩;
    dsimp at he,
    { exact sum.inl a },
    { exact sum.inr (sum.inl ⟨
      ⟨a, nat.lt_succ_iff.1 ((left_height_lt_add_height a b).trans_le he)⟩,
      ⟨b, nat.lt_succ_iff.1 ((right_height_lt_add_height a b).trans_le he)⟩⟩) },
    { refine sum.inr (sum.inr ⟨u, a, _⟩),
      rw psi_height at he,
      exact nat.le_of_add_le_add_right he }
  end,
  have hf : function.injective f := begin
    rintro ⟨a | ⟨a, b⟩ | ⟨u, a⟩, he₁⟩;
    rintro ⟨c | ⟨c, d⟩ | ⟨w, c⟩, he₂⟩;
    intro h;
    simp [f] at *;
    assumption
  end,
  apply (mk_le_of_injective hf).trans,
  simp only [mk_prod, mk_sum, lift_uzero, mk_denumerable],
  convert cardinal.add_le_add (Omega_le_aleph v)
    (cardinal.add_le_add (mul_le_mul' hα hα) (mul_le_mul' (omega_le_aleph v) hα)),
  { exact cardinal.mk_ord_out _ },
  { simp only [cardinal.mul_eq_self (omega_le_aleph v), cardinal.add_eq_self (omega_le_aleph v)] }
end

private theorem mk_eq_Union_height (v : ℕ) :
  #(buchholz_exp' v) = #(⋃ h, {e : buchholz_exp' v | e.height ≤ h}) :=
begin
  let f : buchholz_exp' v → ⋃ h, {e : buchholz_exp' v | e.height ≤ h} :=
    λ e', ⟨e', by { rw set.mem_Union, exact ⟨_, le_refl e'.height⟩ }⟩,
  refine le_antisymm
    (@mk_le_of_injective _ _ f (λ e₁ e₂ h, _))
    (@mk_le_of_surjective _ _ f (λ a, ⟨a, _⟩)),
  { simp only [subtype.mk_eq_mk] at h, exact h },
  { simp only [f, subtype.coe_eta] }
end

theorem mk_eq_aleph (v : ℕ) : #(buchholz_exp' v) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { rw mk_eq_Union_height,
    apply le_trans (mk_Union_le _) _,
    rw mk_nat,
    refine le_trans (mul_le_max _ _) (max_le (max_le (omega_le_aleph v) _) (omega_le_aleph v)),
    { rw cardinal.sup_le,
      exact mk_height_le_aleph v } },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective add_iterate.inj, simp },
    { convert cardinal.mk_le_of_injective (@lt_Omega'.inj (v + 1)),
      exact (cardinal.mk_ord_out _).symm } }
end

/-- A well-formed Buchholz expression is one where `Ψ` is only ever called with arguments with value
less than `o`. -/
def well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : set (buchholz_exp' v)
| (lt_Omega' a)  := tt
| (a + b)        := a.well_formed ∧ b.well_formed
| (psi u a)      := a.well_formed ∧ a.value Ψ < o

theorem lt_Omega'_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  (a : (Omega v).ord.out.α) : lt_Omega' a ∈ well_formed v Ψ :=
(rfl : well_formed v Ψ (lt_Omega' a))

theorem lt_Omega_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal)
  {a : ordinal} (ha : a < (Omega v).ord) : lt_Omega ha ∈ well_formed v Ψ :=
lt_Omega'_well_formed v Ψ _

theorem zero_well_formed {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  (0 : buchholz_exp' v) ∈ well_formed v Ψ :=
lt_Omega_well_formed v Ψ _

theorem add_well_formed {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} {e₁ e₂} :
  e₁ ∈ well_formed v Ψ ∧ e₂ ∈ well_formed v Ψ ↔ e₁ + e₂ ∈ well_formed v Ψ :=
iff.rfl

theorem psi_well_formed {o : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} {e : buchholz_exp' v}
  (u : ℕ) : e ∈ well_formed v Ψ ∧ e.value Ψ < o ↔ psi u e ∈ well_formed v Ψ :=
iff.rfl

theorem add_iterate_well_formed {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) :
  add_iterate n ∈ well_formed 0 Ψ :=
begin
  have h := zero_well_formed 0 Ψ,
  induction n with n hn,
  { exact h },
  { rw add_iterate_succ, exact add_well_formed.2 ⟨h, hn⟩ }
end

theorem value_eq_of_extend_psi {o o' : ordinal} (ho : o ≤ o') {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal}
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  {e : buchholz_exp' v} (he : e ∈ well_formed v Ψ) : e.value Ψ = e.value Ψ' :=
begin
  induction e with a a b ha hb u a h,
  { refl },
  { change (a + b).value Ψ = (a + b).value Ψ',
    unfold value,
    rw [ha he.1, hb he.2] },
  { unfold value,
    rw ←(h he.1) at *,
    split_ifs with hΨ hΨ' hΨ',
    { exact H _ _ u },
    { exact (hΨ' (hΨ.trans_le ho)).elim },
    { exact (hΨ he.2).elim },
    { refl } }
end

end buchholz_exp'

/-- The type of well-formed Buchholz expressions. This corresponds to `C` in Buchholz's original
definition. -/
def buchholz_exp (o : ordinal) (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) : Type 0 :=
buchholz_exp'.well_formed v Ψ

instance (o v Ψ) : has_zero (buchholz_exp o v Ψ) :=
⟨⟨0, buchholz_exp'.zero_well_formed v Ψ⟩⟩

instance (o v Ψ) : inhabited (buchholz_exp o v Ψ) :=
⟨0⟩

namespace buchholz_exp

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega' {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) (a : (Omega v).ord.out.α) :
  buchholz_exp o v Ψ :=
⟨_, buchholz_exp'.lt_Omega'_well_formed v Ψ a⟩

/-- A well-formed Buchholz expression from an ordinal less than `Ωᵥ`. -/
def lt_Omega {o : ordinal} {v : ℕ} {a : ordinal} (ha : a < (Omega v).ord)
  (Ψ : Π a, a < o → ℕ → ordinal) : buchholz_exp o v Ψ :=
⟨_, buchholz_exp'.lt_Omega_well_formed v Ψ ha⟩

theorem lt_Omega'.inj {o : ordinal} (v : ℕ) (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (@lt_Omega' o v Ψ) :=
λ a b h, buchholz_exp'.lt_Omega'.inj (subtype.mk.inj h)

/-- The sum of two well-formed Buchholz expressions. -/
instance (o v Ψ) : has_add (buchholz_exp o v Ψ) :=
⟨λ e₁ e₂, ⟨e₁.1 + e₂.1, buchholz_exp'.add_well_formed.2 ⟨e₁.2, e₂.2⟩⟩⟩

/-- The value of a well-formed Buchholz expression when interpreted as an ordinal. -/
def value {o v Ψ} (a : buchholz_exp o v Ψ) : ordinal :=
a.1.value Ψ

/-- A function `Ψ u` applied to a well-formed Buchholz expression with value less than `o`. -/
def psi {o v Ψ} (u : ℕ) {e : buchholz_exp o v Ψ} (he : e.value < o) : buchholz_exp o v Ψ :=
⟨buchholz_exp'.psi u e.1, (buchholz_exp'.psi_well_formed u).2 ⟨e.2, he⟩⟩

@[simp] theorem lt_Omega_value {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) {a : ordinal}
  (ha : a < (Omega v).ord) : (lt_Omega ha Ψ).value = a :=
buchholz_exp'.lt_Omega_value Ψ ha

@[simp] theorem zero_value {o v Ψ} : (0 : buchholz_exp o v Ψ).value = 0 :=
buchholz_exp'.zero_value Ψ

@[simp] theorem add_value {o v Ψ} (e₁ e₂ : buchholz_exp o v Ψ) :
  (e₁ + e₂).value = e₁.value + e₂.value :=
buchholz_exp'.add_value Ψ e₁.val e₂.val

@[simp] theorem psi_value {o v Ψ} (u : ℕ) {e : buchholz_exp o v Ψ} (he : e.value < o) :
  (psi u he).value = Ψ e.value he u :=
buchholz_exp'.psi_value Ψ u he

theorem value_zero {o : ordinal} (ho : o = 0) {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal)
  (e : buchholz_exp o v Ψ) : e.value < (Omega v).ord :=
buchholz_exp'.value_zero ho Ψ _

/-- Transfers a well-formed Buchholz expression for a family of functions to a larger one. -/
def lift {o o' : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (ho : o ≤ o')
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  (e : buchholz_exp o v Ψ) : buchholz_exp o' v Ψ' :=
⟨e.val, begin
  revert e,
  rintro ⟨e, he⟩,
  dsimp,
  induction e with a a b ha hb u a ha,
  { exact buchholz_exp'.lt_Omega'_well_formed v Ψ' a },
  { exact buchholz_exp'.add_well_formed.2 ⟨ha he.1, hb he.2⟩ },
  { refine (buchholz_exp'.psi_well_formed u).2 ⟨ha he.1, _⟩,
    rw ←buchholz_exp'.value_eq_of_extend_psi ho H he.1,
    exact he.2.trans_le ho }
end⟩

/-- The hypothesis needed to use lift on an unbounded family of functions. -/
theorem lift_H {o o' : ordinal} (ho : o ≤ o') (Ψ : ordinal → ℕ → ordinal) (a) (ha : a < o) (u) :
  (λ a (ha : a < o) u, Ψ a u) a ha u = (λ a (ha : a < o') u, Ψ a u) a (ha.trans_le ho) u :=
rfl

@[simp] theorem lift_value {o o' : ordinal} {v : ℕ} {Ψ : Π a, a < o → ℕ → ordinal} (ho : o ≤ o')
  {Ψ' : Π a, a < o' → ℕ → ordinal} (H : ∀ a (ha : a < o) u, Ψ a ha u = Ψ' a (ha.trans_le ho) u)
  (e : buchholz_exp o v Ψ) : (lift ho H e).value = e.value :=
begin
  revert e,
  rintro ⟨e, he⟩,
  unfold lift value,
  induction e with a a b ha hb u a ha,
  { refl },
  { simp_rw [buchholz_exp'.add_value', ha he.1, hb he.2] },
  { rw [buchholz_exp'.psi_value _ u he.2, buchholz_exp'.psi_value];
    simp_rw ha he.1,
    { exact (H _ _ u).symm },
    { exact he.2.trans_le ho } }
end

/-- An auxiliary definition which gives a denumerable family of well-formed Buchholz expressions. -/
def add_iterate {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) (n : ℕ) : buchholz_exp o 0 Ψ :=
⟨_, buchholz_exp'.add_iterate_well_formed Ψ n⟩

theorem add_iterate.inj {o : ordinal} (Ψ : Π a, a < o → ℕ → ordinal) :
  function.injective (add_iterate Ψ) :=
λ a b h, buchholz_exp'.add_iterate.inj (subtype.mk.inj h)

theorem mk_eq_aleph {o : ordinal} {v : ℕ} (Ψ : Π a, a < o → ℕ → ordinal) :
  #(buchholz_exp o v Ψ) = cardinal.aleph v :=
begin
  apply le_antisymm,
  { rw ←buchholz_exp'.mk_eq_aleph,
    exact mk_le_of_injective (λ a b h, subtype.ext_val h) },
  { induction v with v hv,
    { convert cardinal.mk_le_of_injective (add_iterate.inj Ψ), simp },
    { convert cardinal.mk_le_of_injective (lt_Omega'.inj (v + 1) Ψ),
      exact (cardinal.mk_ord_out _).symm } }
end

end buchholz_exp

/-- Buchholz's `Ψ` function. -/
def buchholz : ordinal → ℕ → ordinal.{0} :=
wf.fix $ λ o Ψ v, mex (@buchholz_exp.value o v Ψ)

theorem buchholz_def' : ∀ o, buchholz o = λ v, mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
wf.fix_eq _

theorem buchholz_def (o : ordinal) (v : ℕ) :
  buchholz o v = mex (@buchholz_exp.value o v (λ a _, buchholz a)) :=
by rw buchholz_def'

theorem value_ne_buchholz {o v} :
  ∀ e : buchholz_exp o v (λ a _, buchholz a), e.value ≠ buchholz o v :=
by { rw buchholz_def, apply ne_mex }

theorem exists_of_lt_buchholz {o a : ordinal} {v : ℕ} (ha : a < buchholz o v) :
  ∃ e : buchholz_exp o v (λ a _, buchholz a), e.value = a :=
by { rw buchholz_def at ha, exact exists_of_lt_mex ha }

theorem Omega_le_buchholz (o : ordinal) (v : ℕ) : (Omega v).ord ≤ buchholz o v :=
begin
  rw buchholz_def,
  by_contra' h,
  exact ne_mex _ (buchholz_exp.lt_Omega h _) (buchholz_exp.lt_Omega_value _ _)
end

theorem buchholz_zero (v : ℕ) : buchholz 0 v = (Omega v).ord :=
begin
  refine le_antisymm _ (Omega_le_buchholz 0 v),
  rw buchholz_def,
  exact (mex_le_lsub _).trans (lsub_le.2 (buchholz_exp.value_zero rfl _))
end

theorem principal_add_buchholz (o : ordinal) (v : ℕ) : principal (+) (buchholz o v) :=
begin
  by_contra h,
  rcases exists_lt_add_of_not_principal_add h with ⟨a, b, ha, hb, hab⟩,
  rcases exists_of_lt_buchholz ha with ⟨e₁, rfl⟩,
  rcases exists_of_lt_buchholz hb with ⟨e₂, rfl⟩,
  rw ←buchholz_exp.add_value at hab,
  exact value_ne_buchholz _ hab
end

theorem buchholz_lt_Omega (o : ordinal) (v : ℕ) : buchholz o v < (Omega (v + 1)).ord :=
begin
  rw buchholz_def,
  convert mex_lt_ord_succ_mk.{0 0} buchholz_exp.value,
  rw [buchholz_exp.mk_eq_aleph, ←aleph_succ],
  refl
end

/-- Buchholz's psi function is strictly monotonic in its subscript. -/
theorem buchholz_strict_mono (o : ordinal) : strict_mono (buchholz o) :=
λ a b h, (buchholz_lt_Omega o a).trans_le $
  (ord_le_ord.2 (Omega_strict_mono.monotone (nat.succ_le_iff.2 h))).trans (Omega_le_buchholz o b)

/-- Buchholz's psi function is monotonic in its ordinal argument. -/
theorem buchholz_monotone (v : ℕ) : monotone (function.swap buchholz v) :=
λ a b h, begin
  unfold function.swap,
  rw [buchholz_def, buchholz_def],
  apply mex_monotone,
  rintros o ⟨e, he⟩,
  use buchholz_exp.lift h (buchholz_exp.lift_H h buchholz) e,
  rw ←he,
  exact buchholz_exp.lift_value h _ e
end

end ordinal
