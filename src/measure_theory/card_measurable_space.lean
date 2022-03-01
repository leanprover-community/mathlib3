import measure_theory.measurable_space_def
import set_theory.cardinal
import set_theory.cardinal_ordinal

/-! ### Cardinal of sigma-algebras -/

universe u
variables {α : Type u}

open_locale cardinal
open cardinal set


lemma glou (α β : Type u) :
  #(α ⊕ β) = # α + # β :=
rfl -- ou rw cardinal.add_def


theorem add_le_of_le {a b c : cardinal} (hc : ω ≤ c)
  (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
(add_le_add h1 h2).trans $ le_of_eq $ add_eq_self hc

instance (o : ordinal.{u}) : has_lt (o.out.α) := ⟨o.out.r⟩
instance (o : ordinal.{u}) : has_well_founded o.out.α := ⟨has_lt.lt, o.out.wo.wf⟩
theorem wf (o : ordinal.{u}): @well_founded o.out.α (<) := o.out.wo.wf
theorem ordinal.out_induction {o : ordinal.{u}} {p : o.out.α → Prop} (i : o.out.α)
  (h : ∀ j, (∀ k, k < j → p k) → p j) : p i :=
o.out.wo.wf.induction i h

def induction_generate_from (s : set (set α)) :
  (cardinal.ord (aleph 1 : cardinal.{u})).out.α → set (set α)
| i := s ∪ {∅} ∪ (λ (t : set α), tᶜ) '' (⋃ j : {j // j < i}, induction_generate_from j.1)
      ∪ (set.range (λ (f : ℕ → (⋃ j : {j // j < i}, induction_generate_from j.1)), (⋃ n, (f n).1)))
using_well_founded {dec_tac := `[exact j.2]}

lemma zoug (s : set (set α)) (i : (cardinal.ord (aleph 1 : cardinal.{u})).out.α) :
  #(my_beautiful_induction s i : Type u) ≤ (1 + #s) * 2 ^ (ω : cardinal.{u}) :=
begin
  have A : ω ≤ (1 + #s) * 2 ^ (ω : cardinal.{u}), from calc
  (ω : cardinal.{u}) ≤ 1 * 2 ^ (ω : cardinal.{u}) + 0 :
      by { rw [one_mul, add_zero], exact le_of_lt (cardinal.cantor _) }
    ... ≤ (1 + #s) * 2 ^ (ω : cardinal.{u}) :
      by { rw add_mul, exact add_le_add le_rfl bot_le },
  apply ordinal.out_induction i,
  assume i IH,
  rw [my_beautiful_induction],
  apply_rules [(mk_union_le _ _).trans, add_le_of_le A, mk_image_le.trans, mk_range_le.trans,
    (mk_Union_le _).trans],
  { calc #s ≤ 0 + #s * 1 : by rw [zero_add, mul_one]
    ... ≤ (1 + # ↥s) * 2 ^ (ω : cardinal.{u}) :
    begin
      rw add_mul,
      refine add_le_add bot_le _,
      exact mul_le_mul' le_rfl (one_le_iff_pos.2 ((nat_lt_omega 0).trans (cardinal.cantor _))),
    end },
  { calc # ({∅} : set (set α)) = 1 + 0 : by simp
    ... ≤ (1 + # ↥s) * 2 ^ (ω : cardinal.{u}) :
      begin
        rw [add_mul, one_mul],
        exact add_le_add (one_le_iff_pos.2 ((nat_lt_omega 0).trans (cardinal.cantor _))) bot_le,
      end },
  {
  }
end


theorem card_generate_measurable_le (s : set (set α)) :
  #{t // generate_measurable s t} ≤ #(s : Type u) * 2 ^ (aleph 0 : cardinal.{u}) :=
begin

end
