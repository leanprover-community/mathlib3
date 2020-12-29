import category_theory.sites.sheaf_of_types

universes v u

namespace category_theory

variables {C : Type u} [small_category C]

variables {P : Cᵒᵖ ⥤ Type u}
variables (J₁ J₂ : grothendieck_topology C)

/--
A sieve is closed for the Grothendieck topology if it contains every arrow it covers. In the case
of the usual topology on a topological space, this means that the open cover contains every open
set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def grothendieck_topology.is_closed {X : C} (S : sieve X) : Prop :=
∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.covers S f → S f

/-- If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains. -/
lemma grothendieck_topology.covers_iff_mem_of_closed {X : C} {S : sieve X}
  (h : J₁.is_closed S) {Y : C} (f : Y ⟶ X) :
  J₁.covers S f ↔ S f :=
⟨h _, J₁.arrow_max _ _⟩

/-- Being `J`-closed is stable under pullback. -/
lemma grothendieck_topology.is_closed_pullback {X Y : C} (f : Y ⟶ X) (S : sieve X) :
  J₁.is_closed S → J₁.is_closed (S.pullback f) :=
begin
  intros hS Z g hg,
  apply hS (g ≫ f),
  rwa [J₁.covers_iff, sieve.pullback_comp],
end

/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
@[simps]
def grothendieck_topology.close {X : C} (S : sieve X) : sieve X :=
{ arrows := λ Y f, J₁.covers S f,
  downward_closed' := λ Y Z f hS, J₁.arrow_stable _ _ hS }

/-- Any sieve is smaller than its closure. -/
lemma grothendieck_topology.le_close {X : C} (S : sieve X) : S ≤ J₁.close S :=
λ Y g hg, J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

/--
The closure of a sieve `S` is the largest closed sieve which contains `S` (justifying the name
"closure").
-/
lemma grothendieck_topology.le_close_of_is_closed {X : C} {S T : sieve X}
  (h : S ≤ T) (hT : J₁.is_closed T) :
  J₁.close S ≤ T :=
λ Y f hf, hT _ (J₁.superset_covering (sieve.pullback_monotone f h) hf)

/-- The closure of a sieve is closed. -/
lemma grothendieck_topology.close_is_closed {X : C} (S : sieve X) : J₁.is_closed (J₁.close S) :=
λ Y g hg, J₁.arrow_trans g _ S hg (λ Z h hS, hS)

/-- The sieve `S` is closed iff its closure is equal to itself. -/
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

lemma grothendieck_topology.close_mono {X : C} : monotone (J₁.close : sieve X → sieve X) :=
λ S₁ S₂ h, J₁.le_close_of_is_closed (le_trans h (J₁.le_close S₂)) (J₁.close_is_closed S₂)

/-- Closing under `J` is stable under pullback. -/
lemma grothendieck_topology.pullback_close {X Y : C} (f : Y ⟶ X) (S : sieve X) :
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

lemma grothendieck_topology.close_idem {X : C} (S : sieve X) :
  J₁.close (J₁.close S) = J₁.close S :=
le_antisymm
  (J₁.le_close_of_is_closed (le_refl (J₁.close S)) (J₁.close_is_closed S))
  (J₁.close_mono (J₁.le_close S))

/--
The sieve `S` is in the topology iff its closure is the maximal sieve. This shows that the closure
operator determines the topology.
-/
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

/--
The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simps]
def functor.closed_sieves : Cᵒᵖ ⥤ Type u :=
{ obj := λ X, {S : sieve X.unop // J₁.is_closed S},
  map := λ X Y f S, ⟨S.1.pullback f.unop, J₁.is_closed_pullback f.unop _ S.2⟩ }

/-- The presheaf of `J`-closed sieves is a `J`-sheaf. -/
lemma classifier_is_sheaf : presieve.is_sheaf J₁ (functor.closed_sieves J₁) :=
begin
  intros X S hS,
  rw ← presieve.is_separated_for_and_exists_is_amalgamation_iff_sheaf_for,
  refine ⟨_, _⟩,
  { rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂,
    ext,
    dsimp only [subtype.coe_mk],
    rw [← J₁.covers_iff_mem_of_closed hM, ← J₁.covers_iff_mem_of_closed hN],
    have q : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (hg : S g), M.pullback g = N.pullback g,
    { intros Z g hg,
      apply congr_arg subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm) },
    have MSNS : M ⊓ S = N ⊓ S,
    { ext Z g,
      rw [sieve.inter_apply, sieve.inter_apply, and_comm (N g), and_comm],
      apply and_congr_right,
      intro hg,
      rw [sieve.pullback_eq_top_iff_mem, sieve.pullback_eq_top_iff_mem, q g hg] },
    split,
    { intro hf,
      rw J₁.covers_iff,
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left),
      rw ← MSNS,
      apply J₁.arrow_intersect f M S hf (J₁.pullback_stable _ hS) },
    { intro hf,
      rw J₁.covers_iff,
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left),
      rw MSNS,
      apply J₁.arrow_intersect f N S hf (J₁.pullback_stable _ hS) } },
  { intros x hx,
    rw presieve.compatible_iff_sieve_compatible at hx,
    let M := sieve.bind S (λ Y f hf, (x f hf).1),
    have : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1,
    { intros Y f hf,
      apply le_antisymm,
      { rintro Z u ⟨W, g, f', hf', (hg : (x f' hf').1 _), c⟩,
        rw [sieve.pullback_eq_top_iff_mem,
          ←(show (x (u ≫ f) _).1 = (x f hf).1.pullback u, from congr_arg subtype.val (hx f u hf))],
        simp_rw ← c,
        rw (show (x (g ≫ f') _).1 = _, from congr_arg subtype.val (hx f' g hf')),
        apply sieve.pullback_eq_top_of_mem _ hg },
      { apply sieve.le_pullback_bind S (λ Y f hf, (x f hf).1) } },
    refine ⟨⟨_, J₁.close_is_closed M⟩, _⟩,
    { intros Y f hf,
      ext1,
      dsimp,
      rw [← J₁.pullback_close, this _ hf],
      apply le_antisymm (J₁.le_close_of_is_closed (le_refl _) (x f hf).2) (J₁.le_close _) } },
end

/-- If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. -/
lemma opposite {J₁ J₂ : grothendieck_topology C}
  (h : presieve.is_sheaf J₁ (functor.closed_sieves J₂)) :
  J₁ ≤ J₂ :=
λ X S hS,
begin
  rw ← J₂.close_eq_top_iff_mem,
  have : J₂.is_closed (⊤ : sieve X),
  { intros Y f hf,
    trivial },
  suffices : (⟨J₂.close S, J₂.close_is_closed S⟩ : subtype _) = ⟨⊤, this⟩,
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

/-- If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂`. -/
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

/--
A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simps]
def topology_of_closure_operator
  (c : Π ⦃X : C⦄, sieve X → sieve X)
  (inc : Π ⦃X : C⦄ (S : sieve X), S ≤ c S)
  (mono : Π ⦃X : C⦄, monotone (@c X))
  (idem : Π ⦃X : C⦄ (S : sieve X), c (c S) = c S)
  (pb : Π ⦃X Y : C⦄ (f : Y ⟶ X) (S : sieve X), c (S.pullback f) = (c S).pullback f) :
  grothendieck_topology C :=
{ sieves := λ X, {S | c S = ⊤},
  top_mem' := λ X, top_unique (inc ⊤),
  pullback_stable' := λ X Y S f hS,
  begin
    rw set.mem_set_of_eq at hS,
    rw [set.mem_set_of_eq, pb, hS, sieve.pullback_top],
  end,
  transitive' := λ X S hS R hR,
  begin
    rw set.mem_set_of_eq at hS,
    rw [set.mem_set_of_eq, ← idem, eq_top_iff, ← hS],
    apply mono (λ Y f hf, _),
    rw [sieve.pullback_eq_top_iff_mem, ← pb],
    apply hR hf,
  end }

/--
The topology given by the closure operator `J.close` on a Grothendieck topology is the same as `J`.
-/
lemma same_topology :
  topology_of_closure_operator (λ X, J₁.close)
    (λ X, J₁.le_close)
    (λ X, J₁.close_mono)
    (λ X, J₁.close_idem)
    (λ X Y, J₁.pullback_close) = J₁ :=
begin
  ext X S,
  apply grothendieck_topology.close_eq_top_iff_mem,
end

lemma same_operator
  (c : Π ⦃X : C⦄, sieve X → sieve X)
  (inc : Π ⦃X : C⦄ (S : sieve X), S ≤ c S)
  (mono : Π ⦃X : C⦄, monotone (@c X))
  (idem : Π ⦃X : C⦄ (S : sieve X), c (c S) = c S)
  (pb : Π ⦃X Y : C⦄ (f : Y ⟶ X) (S : sieve X), c (S.pullback f) = (c S).pullback f)
  (X : C) (S : sieve X) :
  (topology_of_closure_operator c inc mono idem pb).close S = c S :=
begin
  ext,
  change c (sieve.pullback f S) = ⊤ ↔ (c S) f,
  rw [pb, sieve.pullback_eq_top_iff_mem],
end

end category_theory
