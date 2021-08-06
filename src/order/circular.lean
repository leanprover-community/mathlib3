/-
Copyright (c) 2021 Yaël Dillies, Kendall Frey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kendall Frey
-/
import data.set.basic

/-!
# Circular order hierarchy


## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/

class has_btw (α : Type*) :=
(btw : α → α → α → Prop)

export has_btw (btw)

class has_sbtw (α : Type*) :=
(sbtw : α → α → α → Prop)

export has_sbtw (sbtw)

/-! ### Circular preorders -/

class circular_preorder (α : Type*) extends has_btw α, has_sbtw α :=
(btw_refl_left (a b : α) : btw a a b)
(btw_refl_right (a b : α) : btw a b b)
(btw_trans_left (a b c d : α) : btw a b c → btw b d c → btw a d c)
(btw_trans_right (a b c d : α) : btw a b c → btw a c d → btw a b d)
(sbtw := λ a b c, btw a b c ∧ ¬btw c b a)
(sbtw_cyclic_left (a b c : α) : sbtw a b c → sbtw b c a)
(sbtw_iff_btw_not_btw (a b c : α) : sbtw a b c ↔ (btw a b c ∧ ¬btw c b a) . order_laws_tac)

export circular_preorder (btw_refl_left) (btw_refl_right)

section circular_preorder
variables {α : Type*} [circular_preorder α]

lemma btw_rfl_left {a b : α} : btw a a b :=
btw_refl_left _ _

lemma btw_rfl_right {a b : α} : btw a b b :=
btw_refl_right _ _

lemma btw_refl (a : α) : btw a a a :=
btw_rfl_left
lemma btw_rfl {a : α} : btw a a a :=
btw_refl _

lemma btw_trans_left : ∀ {a b c d : α}, btw a b c → btw b d c → btw a d c :=
circular_preorder.btw_trans_left
--alias btw_trans        ← has_btw.btw.trans
lemma has_btw.btw.trans_left {a b c d : α} (h : btw a b c) : btw b d c → btw a d c :=
btw_trans_left h

lemma btw_trans_right : ∀ {a b c d : α}, btw a b c → btw a c d → btw a b d :=
circular_preorder.btw_trans_right
--alias btw_trans        ← has_btw.btw.trans
lemma has_btw.btw.trans_right {a b c d : α} (h : btw a b c) : btw a c d → btw a b d :=
btw_trans_right h

lemma sbtw_iff_btw_not_btw : ∀ {a b c : α}, sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
circular_preorder.sbtw_iff_btw_not_btw

lemma btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
(sbtw_iff_btw_not_btw.1 h).1
--alias btw_of_sbtw        ← has_sbtw.sbtw.btw
lemma has_sbtw.sbtw.btw {a b c : α} (h : sbtw a b c) : btw a b c :=
btw_of_sbtw h

lemma not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
(sbtw_iff_btw_not_btw.1 h).2
--alias not_btw_of_sbtw        ← has_sbtw.sbtw.not_btw
lemma has_sbtw.sbtw.not_btw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
not_btw_of_sbtw h

lemma not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a :=
λ h', h'.not_btw h
--alias not_btw_of_sbtw        ← has_sbtw.sbtw.not_btw
lemma has_btw.btw.not_sbtw {a b c : α} (h : btw a b c) : ¬sbtw c b a :=
not_sbtw_of_btw h

lemma sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩
--alias sbtw_of_btw_not_btw        ← has_btw.btw.sbtw_of_not_btw
lemma has_btw.btw.sbtw_of_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
sbtw_of_btw_not_btw habc hcba

lemma sbtw_cyclic_left : ∀ {a b c : α}, sbtw a b c → sbtw b c a :=
circular_preorder.sbtw_cyclic_left
--alias sbtw_cyclic_left        ← has_sbtw.sbtw.cyclic_left
lemma has_sbtw.sbtw.cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
sbtw_cyclic_left h

lemma sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
h.cyclic_left.cyclic_left
--alias sbtw_cyclic_right        ← has_sbtw.sbtw.cyclic_right
lemma has_sbtw.sbtw.cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
sbtw_cyclic_right h

/-- The order of the `↔` has been chosen so that `rw sbtw_cyclic` cycles to the right while
`rw ←sbtw_cyclic` cycles to the left (thus following the prepended arrow). -/
lemma sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

lemma sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬ sbtw c b a :=
h.btw.not_sbtw
--alias sbtw_asymm        ← has_sbtw.sbtw.not_sbtw
lemma has_sbtw.sbtw.not_sbtw {a b c : α} (h : sbtw a b c) : ¬ sbtw c b a :=
sbtw_asymm h

lemma sbtw_irrefl_left_right {a b : α} : ¬ sbtw a b a := λ h, h.not_btw h.btw
lemma sbtw_irrefl (a : α) : ¬ sbtw a a a := sbtw_irrefl_left_right
lemma sbtw_irrefl_left {a b : α} : ¬ sbtw a a b := λ h, sbtw_irrefl_left_right h.cyclic_left
lemma sbtw_irrefl_right {a b : α} : ¬ sbtw a b b := λ h, sbtw_irrefl_left_right h.cyclic_right
example {a b : α} : btw a a b :=
begin
  have := sbtw_irrefl_left,
  rw sbtw_iff_btw_not_btw at this,
  simp at this,
end

end circular_preorder

/-! ### Circular partial orders -/

class circular_partial_order (α : Type*) extends circular_preorder α :=
(btw_antisymm : ∀ a b c, btw a b c → btw c b a → a = c)

section circular_partial_order
variables {α : Type*} [circular_partial_order α]

lemma btw_antisymm : ∀ {a b c : α}, btw a b c → btw c b a → a = c :=
circular_partial_order.btw_antisymm
--alias btw_antisymm        ← has_btw.btw.antisymm
lemma has_btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = c :=
btw_antisymm h

end circular_partial_order

/-! ### Circular orders -/

class circular_order (α : Type*) extends circular_partial_order α :=
(btw_total : ∀ a b c : α, btw a b c ∨ btw c b a)

export circular_order (btw_total)

section circular_order
variables {α : Type*} [circular_order α]

lemma btw_left_right (a b : α) : btw a b a :=
(or_self _).1 (btw_total a b a)

lemma sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬ btw c b a :=
begin
  rw sbtw_iff_btw_not_btw,
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left,
end

lemma btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬ sbtw c b a :=
iff_not_comm.1 sbtw_iff_not_btw

lemma btw_refl_right (a b : α) : btw a a b :=
begin
  have := btw_total a a b,
  obtain rfl | h := eq_or_ne a b,
  { exact btw_rfl },
  sorry
end

end circular_order

/-! ### Circular intervals -/

namespace set

section circular_preorder
variables {α : Type*} [circular_preorder α]

/-- Circular interval closed-closed -/
def cIcc (a b : α) : set α := {x | btw a x b}

/-- Circular interval closed-open -/
def cIco (a b : α) : set α := {x | btw a x b ∧ ¬btw a b x}

/-- Circular interval open-closed -/
def cIoc (a b : α) : set α := {x | btw a x b ∧ ¬btw x a b}

/-- Circular interval open-open -/
def cIoo (a b : α) : set α := {x | sbtw a x b}

@[simp] lemma mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b := iff.rfl
@[simp] lemma mem_cIco {a b x : α} : x ∈ cIco a b ↔ btw a x b ∧ ¬btw a b x := iff.rfl
@[simp] lemma mem_cIoc {a b x : α} : x ∈ cIoc a b ↔ btw a x b ∧ ¬btw x a b := iff.rfl
@[simp] lemma mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b := iff.rfl

lemma left_mem_cIcc (a b : α) : a ∈ cIcc a b := btw_rfl_left
lemma right_mem_cIcc (a b : α) : b ∈ cIcc a b := btw_rfl_right

lemma left_mem_cIco (a b : α) : a ∈ cIco a b := ⟨btw_rfl_left, sorry⟩
lemma right_not_mem_cIco (a b : α) : b ∉ cIco a b := λ h, h.2 btw_rfl_right


end circular_preorder

section circular_order
variables {α : Type*} [circular_order α]

lemma compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a :=
begin
  ext,
  rw [set.mem_cIoo, sbtw_iff_not_btw],
  refl,
end

lemma compl_cIco {a b : α} : (cIoo a b)ᶜ = cIcc b a :=
begin
  ext,
  rw [set.mem_cIcc, btw_iff_not_sbtw],
  refl,
end

end circular_order

end set

/-! ### Dual constructions -/

section order_dual

instance (α : Type*) [has_btw α] : has_btw (order_dual α) := ⟨λ a b c : α, btw c b a⟩
instance (α : Type*) [has_sbtw α] : has_sbtw (order_dual α) := ⟨λ a b c : α, sbtw c b a⟩

instance (α : Type*) [h : circular_preorder α] : circular_preorder (order_dual α) :=
{ btw_refl_left := λ a b, btw_refl_right b a,
  btw_refl_right := λ a b, btw_refl_left b a,
  btw_trans_left := λ a b c d habc hbdc, hbdc.trans_right habc,
  btw_trans_right := λ a b c d habc hacd, hacd.trans_left habc,
  sbtw_cyclic_left := λ a b c, sbtw_cyclic_right,
  sbtw_iff_btw_not_btw := λ a b c, @sbtw_iff_btw_not_btw α _ c b a,
  .. order_dual.has_btw α,
  .. order_dual.has_sbtw α }

instance (α : Type*) [circular_partial_order α] : circular_partial_order (order_dual α) :=
{ btw_antisymm := λ a b c habc hcba, @btw_antisymm α _ _ _ _ hcba habc,
  .. order_dual.circular_preorder α }

instance (α : Type*) [circular_order α] : circular_order (order_dual α) :=
{ btw_total := λ a b c, btw_total c b a, .. order_dual.circular_partial_order α }


end order_dual
