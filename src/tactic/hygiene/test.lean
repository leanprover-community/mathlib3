import tactic.hygiene.basic
import algebra.category.CommRing.basic
import ring_theory.ideals

universes w₁ v₁ v₂ u₁ u₂

open category_theory

set_option pp.universes true


instance hygienic_zero_eq_one : bundled_hygienic.{u₁} (λ (α : Type u₁) [comm_ring α], by exactI (0 : α) = (1 : α)) :=
begin
  dsimp [bundled_hygienic],
  fsplit,
  intros X Y f,
  fsplit,
  { intro h,
    have t := congr_arg f.hom h,
    rw [is_ring_hom.map_zero f.hom] at t,
    rw [is_ring_hom.map_one f.hom] at t,
    exact t },
  { intro h,
    have t := congr_arg f.inv h,
    rw [is_ring_hom.map_zero f.inv] at t,
    rw [is_ring_hom.map_one f.inv] at t,
    exact t },
end

example (X Y : CommRing.{u₁}) (f : X ≅ Y) (x : units.{u₁} (X.α)) :
  (f.inv : Y →* X) ((f.hom : X →* Y) x) = x :=
begin

end

instance iso_functorial_units : iso_functorial.{u₁ u₁} (λ (X : CommRing.{u₁}), units (X.α)) :=
{ map := λ X Y f,
  { hom := λ u, units.map (f.hom : X →* Y) u,
    inv := λ u, units.map (f.inv : Y →* X) u,
    hom_inv_id' := begin
      dsimp,
      ext1,
      dsimp,
      ext1, simp, extract_goal end } }


-- instance iso_functorial_units_crap : iso_functorial.{u₁ u₁} (λ (X : (forget CommRing.{u₁}).elements), units ((X.1).α)) :=
-- { map := λ X Y f, sorry }

set_option pp.universes false

example :
  hygienic.{u₁}
  (λ (e : (as_core_functor (λ (X : (forget CommRing.{u₁}).elements), units ((X.1).α))).elements),
     (of_core (e.1)).2 = (e.2).val) :=
begin
split,
intros X Y f,
split,
intro h,
cases X, cases Y, cases f,
cases f_hom,
dsimp at *,
subst f_hom_property,
sorry,
sorry,
end

instance hygienic_is_unit :
  hygienic.{u₁ u₁+1}
  (λ (X : CommRing.{u₁}), ∀ (a : X.α), is_unit.{u₁} a ∨ is_unit.{u₁} (1 + -a)) :=
begin
  apply @hygienic_forall_forget.{u₁} CommRing _ _ _,
  apply @hygienic_or _ _ _ _ _ _,
  dsimp [is_unit],
  apply @hygienic_exists_iso_functorial _ _ _ _ _ _,
  apply_instance,
  extract_goal,
end

instance : bundled_hygienic.{u₁} is_local_ring.{u₁} :=
begin
  have t : (is_local_ring = λ (x : Type u₁) [comm_ring x], by exactI is_local_ring x), funext, refl,
  rw t,
  clear t,
  conv {
    congr, funext, dsimp [is_local_ring],
  },
  dsimp [bundled_hygienic],
  apply @hygienic_and _ _ _ _ _ _,
  apply @hygienic_not _ _ _ _,
  apply hygienic_zero_eq_one,
  apply hygienic_is_unit,
end


-- instance : functorial.{u₁ u₁} local_ring.{u₁} :=
-- begin
--
-- end
