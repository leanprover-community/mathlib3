import category_theory.sites.grothendieck
import category_theory.sites.cover_preserving
import category_theory.sites.cover_lifting

universes v₁ v₂ u₁ u₂

namespace category_theory
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] (F : C ⥤ D)
variables (J : grothendieck_topology D)

def induced_topology : grothendieck_topology C :=
{ sieves := λ X S,
    ∀ (K : grothendieck_topology C)
      (H : ∀ ⦃Y⦄ (T : J (F.obj Y)), T.val.functor_pullback F ∈ K Y), S ∈ K X,
  top_mem' := λ X K _, K.top_mem _,
  pullback_stable' := λ X Y S f hf K H, K.pullback_stable f (hf K H),
  transitive' := λ X S hS S' f K H, K.transitive (hS K H) _ (λ _ _ hg, f hg K H) }

lemma is_cover_of_functor_pullback {X : C} (S: J (F.obj X)) :
  S.val.functor_pullback F ∈ (induced_topology F J) X := λ K H, H S

def induced_cover_lifting : cover_lifting (induced_topology F J) J F :=
{ cover_lift := λ U S hS, is_cover_of_functor_pullback F J ⟨S, hS⟩ }

def induced_topology_of_fully_faithful [full F] [faithful F]
  (H : ∀ ⦃X⦄ (T : J (F.obj X)), (T.val.functor_pullback F).functor_pushforward F ∈ J (F.obj X)) :
  grothendieck_topology C :=
{ sieves := λ X S, ∃ (T : J (F.obj X)), S = T.val.functor_pullback F,
  top_mem' := λ X, by { use ⟨_, J.top_mem _⟩, simp },
  pullback_stable' := λ X Y S f ⟨T, eq⟩,
  begin
    clear_, cases eq,
    change Exists _,
    use ⟨_, J.pullback_stable (F.map f) T.property⟩,
    ext,
    change T _ ↔ T _,
    rw F.map_comp
  end,
  transitive' := λ X S ⟨T, eq⟩ S' H',
  begin
    clear_, cases eq,
    change Exists _,
    use S'.functor_pushforward F,
    { apply J.transitive (H T),
      rintros Y _ ⟨Z, g, i, h, rfl⟩,
      rw sieve.pullback_comp,
      apply J.pullback_stable i,
      obtain ⟨T, eq⟩ := H' h,
      refine J.superset_covering _ (H T),
      rw ← eq,
      conv_lhs { rw ←(sieve.fully_faithful_functor_galois_coinsertion F X).u_l_eq S' },
      generalize : S'.functor_pushforward F = T',
      rintros Y' _ ⟨Z', g', i', h', rfl⟩,
      change T' _,
      rw [category.assoc, ←F.map_comp],
      exact T'.downward_closed h' i' },
    rw (sieve.fully_faithful_functor_galois_coinsertion F X).u_l_eq S'
  end }

lemma pullback_in_induced [full F] [faithful F] (H) {X} (T : J (F.obj X)) :
  T.val.functor_pullback F ∈ induced_topology_of_fully_faithful F J H X := by use T

lemma induced_topology_of_fully_faithful_is_induced [full F] [faithful F] (H) {X : C} (S : sieve X) :
    induced_topology F J = induced_topology_of_fully_faithful F J H :=
begin
  ext X S,
  split,
  { intro hS,
    exact hS (induced_topology_of_fully_faithful F J H) (λ _ T, pullback_in_induced F J H T) },
  rintros ⟨T, rfl⟩ K hK,
  apply hK,
end

end category_theory
