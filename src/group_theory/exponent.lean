
import group_theory.order_of_element
import algebra.punit_instances

universe u

open_locale classical

def exponent_exists (G : Type u) [monoid G] := ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

noncomputable def exponent (G : Type u) [monoid G] :=
if h : exponent_exists G then nat.find h else 0

lemma exponent_pos_of_exists (G : Type u) [monoid G] (n : ℕ) (hpos : 0 < n)
(hG : ∀ g : G, g ^ n = 1) : 0 < exponent G :=
begin
  rw [exponent, dif_pos] ,
  { have : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1,
      { exact ⟨n, hpos, hG⟩ },
    exact (nat.find_spec this).1,
  },
  { exact ⟨n, hpos, hG⟩ },
end

lemma exponent_min' (G : Type u) [monoid G] (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) :
  exponent G ≤ n :=
begin
  rw [exponent, dif_pos],
  { apply nat.find_min',
    exact ⟨hpos, hG⟩,},
  { exact ⟨n, hpos, hG⟩ },
end

lemma exp_punit_eq_one : exponent punit = 1 :=
begin
  apply le_antisymm,
  { apply exponent_min' _ _ nat.one_pos,
    intro g,
    refl },
  { apply nat.succ_le_of_lt,
    apply exponent_pos_of_exists _ 1 (nat.one_pos),
    intro g,
    refl },
end
