import category_theory.enriched.enriched_over
import algebra.category.Group.monoidal

universes u

open category_theory

namespace AddCommGroup

def forget_tensor (G H : AddCommGroup) :
  (forget AddCommGroup).obj (G ⊗ H) ≅ (forget AddCommGroup).obj G ⊗ (forget AddCommGroup).obj H :=
begin
  have : limits.preserves_limit (limits.pair G H) (forget AddCommGroup) := by apply_instance,
  have : limits.has_limit (limits.pair G H ⋙ forget AddCommGroup) := by apply_instance,
  convert limits.preserves_limit_iso _ (forget AddCommGroup),

end

instance : concrete_monoidal_category AddCommGroup.{u} :=
{ lax_monoidal :=
  { ε := λ _, sorry,
    μ := λ G H x,
    begin
    -- TODO this is too gross,
    -- and depends on the details of how we implemented products in `AddCommGroup`
      -- cases x, fsplit, intro j, cases j,
      -- exact x_val limits.walking_pair.left,
      -- exact x_val limits.walking_pair.right,
      -- intros j j' f, cases f, cases f, cases f, cases j,
      -- refl, refl,
    end }}

example : enriched_over AddCommGroup.{u} AddCommGroup.{u} :=
{ e_hom := λ X Y, AddCommGroup.of (X ⟶ Y),
  e_id := λ X, λ _, 𝟙 _,
  e_comp := λ X Y Z p, p.val (limits.walking_pair.left) ≫ p.val (limits.walking_pair.right), -- that was ugly...
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end AddCommGroup
