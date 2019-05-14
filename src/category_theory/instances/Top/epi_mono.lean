import category_theory.instances.Top.adjunctions
import category_theory.epi_mono

universe u

open category_theory category_theory.instances

namespace category_theory.instances.Top

lemma epi_iff_surjective {X Y : Top.{u}} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  suffices : epi f ↔ epi (forget.map f),
  { rw [this, category_theory.epi_iff_surjective], refl },
  split,
  { apply left_adjoint_preserves_epi adj₂ },
  { apply faithful_reflects_epi }
end

lemma mono_iff_injective {X Y : Top.{u}} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  suffices : mono f ↔ mono (forget.map f),
  { rw [this, category_theory.mono_iff_injective], refl },
  split,
  { apply right_adjoint_preserves_mono adj₁ },
  { apply faithful_reflects_mono }
end

end category_theory.instances.Top
