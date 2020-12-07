import category_theory.sites.sheaf

universes v u

namespace category_theory

variables {C : Type u} [small_category C]

variables {P : Cᵒᵖ ⥤ Type u}
variables (J₁ J₂ : grothendieck_topology C)

def grothendieck_topology.is_closed {X : C} (S : sieve X) : Prop :=
∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.covers S f → S f

lemma grothendieck_topology.covers_iff_mem_of_closed {X : C} {S : sieve X}
  (h : J₁.is_closed S) {Y : C} (f : Y ⟶ X) :
  J₁.covers S f ↔ S f :=
⟨h _, J₁.arrow_max _ _⟩

lemma grothendieck_topology.is_closed_pullback {X Y : C} (f : Y ⟶ X) (S : sieve X) :
  J₁.is_closed S → J₁.is_closed (S.pullback f) :=
begin
  intros hS Z g hg,
  apply hS (g ≫ f),
  rw J₁.covers_iff,
  rw sieve.pullback_comp,
  apply hg
end

def grothendieck_topology.close {X : C} (S : sieve X) : sieve X :=
{ arrows := λ Y f, J₁.covers S f,
  downward_closed' := λ Y Z f hS, J₁.arrow_stable _ _ hS }

lemma grothendieck_topology.le_close {X : C} (S : sieve X) : S ≤ J₁.close S :=
λ Y g hg, J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

lemma grothendieck_topology.le_close_of_is_closed {X : C} {S T : sieve X}
  (h : S ≤ T) (hT : J₁.is_closed T) :
  J₁.close S ≤ T :=
λ Y f hf, hT _ (J₁.superset_covering (sieve.pullback_monotone f h) hf)

lemma grothendieck_topology.close_is_closed {X : C} (S : sieve X) : J₁.is_closed (J₁.close S) :=
λ Y g hg, J₁.arrow_trans g _ S hg (λ Z h hS, hS)

lemma grothendieck_topology.is_closed_iff_close_eq_self {X : C} (S : sieve X) :
  J₁.is_closed S ↔ J₁.close S = S :=
begin
  split,
  { intro h,
    apply le_antisymm,
    { intros Y f hf,
      rw ← J₁.covers_iff_mem_of_closed h,
      apply hf },
    { apply J₁.le_close } },
  { intro e,
    rw ← e,
    apply J₁.close_is_closed }
end

lemma grothendieck_topology.close_eq_top_iff_mem {X : C} (S : sieve X) :
  J₁.close S = ⊤ ↔ S ∈ J₁ X :=
begin
  split,
  { intro h,
    apply J₁.transitive (J₁.top_mem X),
    intros Y f hf,
    change J₁.close S f,
    rw h,
    trivial },
  { intro hS,
    rw eq_top_iff,
    intros Y f hf,
    apply J₁.pullback_stable _ hS }
end

-- def topology_of_closure_operator
--   {c : Π ⦃X : C⦄, sieve X → sieve X}
--   (inc : Π {X : C} (S : sieve X), S ≤ c S)
--   (mono : Π {X : C}, monotone (@c X))
--   (idem : Π {X : C} (S : sieve X), c (c S) = c S)
--   (pb : Π {X Y : C} (f : Y ⟶ X) (S : sieve X), c (S.pullback f) = (c S).pullback f) :
--   grothendieck_topology C :=
-- { sieves := λ X, {S | c S = ⊤},
--   top_mem' := λ X,
--   begin
--     dsimp,
--     rw eq_top_iff,
--     apply inc,
--   end,
--   pullback_stable' := λ X Y S f hS,
--   begin
--     dsimp at hS,
--     dsimp,
--     rw pb,
--     rw hS,
--     rw sieve.pullback_top,
--   end,
--   transitive' := λ X S hS R hR,
--   begin
--     dsimp,
--     dsimp at hS,
--     rw ← idem,
--     rw eq_top_iff,
--     rw ← hS,
--     apply mono,
--     intros Y f hf,
--     rw sieve.pullback_eq_top_iff_mem,
--     rw ← pb,
--     apply hR hf,
--   end }

@[simps]
def classifier : Cᵒᵖ ⥤ Type u :=
{ obj := λ X, {S : sieve X.unop // J₁.is_closed S},
  map := λ X Y f S, ⟨S.1.pullback f.unop, J₁.is_closed_pullback f.unop _ S.2⟩ }

def grothendieck_topology.pullback_close {X Y : C} (f : Y ⟶ X) (S : sieve X) :
  J₁.close (S.pullback f) = (J₁.close S).pullback f :=
begin
  apply le_antisymm,
  { apply J₁.le_close_of_is_closed,
    { apply sieve.pullback_monotone,
      apply J₁.le_close },
    { apply J₁.is_closed_pullback,
      apply J₁.close_is_closed } },
  { intros Z g hg,
    change _ ∈ J₁ _,
    rw ← sieve.pullback_comp,
    apply hg }
end

lemma classifier_is_sheaf : presieve.is_sheaf J₁ (classifier J₁) :=
begin
  intros X S hS,
  rw ← presieve.is_separated_for_and_exists_is_amalgamation_iff_sheaf_for,
  refine ⟨_, _⟩,
  { rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂,
    ext,
    dsimp,
    rw ← J₁.covers_iff_mem_of_closed hM,
    rw ← J₁.covers_iff_mem_of_closed hN,
    have q : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (hg : S g), M.pullback g = N.pullback g,
    { intros Z g hg,
      apply congr_arg subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm) },
    have MSNS : M ⊓ S = N ⊓ S,
    { ext Z g,
      rw sieve.mem_inter,
      rw sieve.mem_inter,
      rw and_comm (N g),
      rw and_comm,
      apply and_congr_right,
      intro hg,
      rw sieve.pullback_eq_top_iff_mem,
      rw sieve.pullback_eq_top_iff_mem,
      rw q g hg },
    have : J₁.covers S f,
      apply J₁.pullback_stable _ hS,
    split,
    { intro hf,
      rw J₁.covers_iff,
      have : J₁.covers (N ⊓ S) f,
        rw ← MSNS,
        apply J₁.arrow_intersect f M S hf this,
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left) this },
    { intro hf,
      rw J₁.covers_iff,
      have : J₁.covers (M ⊓ S) f,
        rw MSNS,
        apply J₁.arrow_intersect f N S hf this,
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left) this } },
  { intros x hx,
    rw presieve.compatible_iff_sieve_compatible at hx,
    let M := sieve.bind S (λ Y f hf, (x f hf).1),
    have : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1,
    { intros Y f hf,
      apply le_antisymm,
      { rintro Z u ⟨W, g, f', hf', (hg : (x f' hf').1 _), c⟩,
        rw sieve.pullback_eq_top_iff_mem,
        rw ←(show (x (u ≫ f) _).1 = (x f hf).1.pullback u, from congr_arg subtype.val (hx f u hf)),
        simp_rw ← c,
        rw (show (x (g ≫ f') _).1 = _, from congr_arg subtype.val (hx f' g hf')),
        apply sieve.pullback_eq_top_of_mem _ hg },
      { apply sieve.le_pullback_bind S (λ Y f hf, (x f hf).1) } },
    refine ⟨⟨J₁.close M, _⟩, _⟩,
    { apply J₁.close_is_closed },
    { intros Y f hf,
      ext1,
      dsimp,
      rw ← J₁.pullback_close,
      rw this _ hf,
      apply le_antisymm,
      apply J₁.le_close_of_is_closed,
      apply le_refl _,
      apply (x f hf).2,
      apply J₁.le_close } },
end

lemma opposite {J₁ J₂ : grothendieck_topology C} (h : presieve.is_sheaf J₁ (classifier J₂)) :
  J₁ ≤ J₂ :=
begin
  intros X S hS,
  rw ← J₂.close_eq_top_iff_mem,
  have : J₂.is_closed (⊤ : sieve X),
  { intros Y f hf,
    trivial },
  suffices : (⟨J₂.close S, J₂.close_is_closed S⟩ : (classifier J₂).obj (opposite.op X)) = ⟨⊤, this⟩,
  { rw subtype.ext_iff at this,
    exact this },
  apply (h S hS).is_separated_for.ext,
  { intros Y f hf,
    ext1,
    dsimp,
    rw [sieve.pullback_top, ← J₂.pullback_close, S.pullback_eq_top_of_mem hf,
        J₂.close_eq_top_iff_mem],
    apply J₂.top_mem },
end

lemma same_topology_iff_same_sheaves {J₁ J₂ : grothendieck_topology C} :
  J₁ = J₂ ↔ (∀ P, presieve.is_sheaf J₁ P ↔ presieve.is_sheaf J₂ P) :=
begin
  split,
  { rintro rfl,
    intro P,
    refl },
  { intro h,
    apply le_antisymm,
    apply opposite,
    rw h,
    apply classifier_is_sheaf,
    apply opposite,
    rw ← h,
    apply classifier_is_sheaf }
end

end category_theory
