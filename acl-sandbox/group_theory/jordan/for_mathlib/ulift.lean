import tactic
import control.ulift

namespace ulift
universes u v w
variables {α : Type u} {β : Type v}

set_option pp.universes true

lemma comp_ulift_eq_ulift_comp {f : α → β} : equiv.ulift ∘ (ulift.map f) = f ∘ equiv.ulift := rfl

/-
Note : this involves 4 universes :

comp_ulift_eq_ulift_comp.{u_1 u_2 u_3 u_4} :
  ⇑equiv.ulift.{u_4 u_2} ∘ ulift.map.{u_1 u_2 u_3 u_4} ?M_3 = ?M_3 ∘ ⇑equiv.ulift.{u_3 u_1}

A discussion with Eric Rodriguez
suggested to make them explicit, so as to have only 3.
If w is another universe, one could write :

lemma comp_ulift_eq_ulift_comp {f : α → β} :
equiv.ulift.{w v} ∘ (ulift.map.{u v w} f) =
  f ∘ equiv.ulift.{w u} := rfl

-- comp_ulift_eq_ulift_comp.{u_1 u_2 u_3} :
--  ⇑equiv.ulift.{u_3 u_2} ∘ ulift.map.{u_1 u_2 u_3 u_3} ?M_3 = ?M_3 ∘ ⇑equiv.ulift.{u_3 u_1}

but then the remaining of the file does not compile anymore. -/

lemma surjective_iff_surjective {f : α → β} :
  function.surjective (ulift.map f) ↔ function.surjective f :=
by rw [← equiv.comp_surjective, comp_ulift_eq_ulift_comp, equiv.surjective_comp]

lemma injective_iff_injective {f : α → β} :
  function.injective (ulift.map f) ↔ function.injective f :=
by rw [← equiv.comp_injective, comp_ulift_eq_ulift_comp, equiv.injective_comp]


lemma bijective_iff_bijective {f : α → β} :
  function.bijective (ulift.map f) ↔ function.bijective f :=
by rw [← equiv.comp_bijective, comp_ulift_eq_ulift_comp, equiv.bijective_comp]

/- Alternative lemma, but the proof requires 4 lines :

lemma bijective_iff_bijective' {f : α → β} :
  function.bijective f ↔ function.bijective (ulift.map f) :=
begin
    unfold function.bijective,
    rw [surjective_iff_surjective, injective_iff_injective],
end

-/

end ulift
