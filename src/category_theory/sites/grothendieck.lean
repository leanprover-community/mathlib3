/- Author: E.W.Ayers.
   This section roughly follows Chapter 3, §1, §2 of Sheaves in Geology and Logic by Saunders Maclane and Ieke M.
 -/

import category_theory.sites.sieves

universes u v w
namespace category_theory

open category_theory limits order lattice

/-- A set of sieves for every object in the category: a candidate to be a Grothendieck topology. -/
def sieve_set (C : Type u) [category.{v} C] := Π (X : C), set (sieve X)

def sieve_set.trivial (C : Type u) [category.{v} C] : sieve_set C := λ X, {⊤}

lemma mem_trivial (C : Type u) [category.{v} C] {X : C} (S : sieve X) :
  S ∈ sieve_set.trivial C X ↔ S = ⊤ :=
set.mem_singleton_iff

/-- A sieve on `X` is dense if for any arrow `f : Y ⟶ X`, there is a `g : Z ⟶ Y` with `g ≫ f ∈ S`. -/
def sieve_set.dense (C : Type u) [category.{v} C] : sieve_set C :=
λ X, {S | ∀ {Y : C} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), S.arrows (g ≫ f)}

/-- The atomic sieve_set just contains all of the non-empty sieves. -/
def sieve_set.atomic (C : Type u) [category.{v} C] : sieve_set C :=
λ X, {S | ∃ {Y} (f : Y ⟶ X), S.arrows f}

open sieve category

/--
Definition of a Grothendieck Topology: a set of sieves `J X` on each object `X` satisfying three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.
-/
class grothendieck {C : Type u} [category.{v} C] (J : sieve_set C) : Prop :=
(max : ∀ X, ⊤ ∈ J X)
(stab : ∀ {X Y : C} (S : sieve X) (h₁ : S ∈ J X) (f : Y ⟶ X), S.pullback f ∈ J Y)
(trans : ∀ ⦃X⦄ (S : sieve X) (hS : S ∈ J X) (R : sieve X), (∀ {Y} (f : Y ⟶ X), S.arrows f → R.pullback f ∈ J Y) → R ∈ J X)

/-- A site is a category equipped with a grothendieck topology. -/
structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : sieve_set C)
[g : grothendieck J]

namespace grothendieck
variables {C : Type u} [category.{v} C]
variables {X Y : C} {S R : sieve X}
variables {J : sieve_set C} [grothendieck J]

def superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X :=
begin
  apply grothendieck.trans _ sjx,
  intros Y h hh,
  rw pullback_eq_top_iff_mem at hh,
  have : R.pullback h = ⊤,
    rw [← top_le_iff, ← hh],
    apply pullback_monotone _ Hss,
  rw this,
  apply grothendieck.max,
end

def covers (J : sieve_set C) (S : sieve X) (f : Y ⟶ X) : Prop := S.pullback f ∈ J Y

lemma arrow_max (f : Y ⟶ X) (S : sieve X) [grothendieck J] (hf : S.arrows f) : covers J S f :=
begin
  rw [covers, (pullback_eq_top_iff_mem f).1 hf],
  apply grothendieck.max,
end
lemma arrow_stab (f : Y ⟶ X) (S : sieve X) (h : covers J S f) {Z : C} (g : Z ⟶ Y) : covers J S (g ≫ f) :=
begin
  rw [covers, pullback_comp],
  apply grothendieck.stab,
  apply h,
end
lemma arrow_trans (f : Y ⟶ X) (S R : sieve X) (h : covers J S f) : (∀ {Z : C} (g : Z ⟶ X), S.arrows g → covers J R g) → covers J R f :=
begin
  intro k,
  apply grothendieck.trans (S.pullback f) h,
  intros Z g hg,
  rw ← pullback_comp,
  apply k (g ≫ f) hg,
end

lemma intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X :=
begin
  apply grothendieck.trans R rj,
  intros Y f Hf,
  have : S.pullback f ≤ (R ⊓ S).pullback f,
    intros Z g hg,
    refine ⟨downward_closed _ Hf _, hg⟩,
  apply superset_covering this,
  apply grothendieck.stab _ sj,
  apply_instance,
end

lemma arrow_intersect (f : Y ⟶ X) (S R : sieve X) (hS : covers J S f) (hR : covers J R f) : covers J (S ⊓ R) f :=
begin
  rw [covers, pullback_inter],
  apply intersection_covering;
  assumption
end

open sieve_set

instance trivial.grothendieck : grothendieck (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _,
  stab := λ X Y S HS h,
  begin
    rw mem_trivial at *,
    rw [HS, pullback_top],
  end,
  trans := λ X S HS R HR,
  begin
    rw [mem_trivial, ← id_mem_iff_eq_top, pullback_eq_top_iff_mem],
    simp only [mem_trivial] at HR,
    apply HR,
    rwa [id_mem_iff_eq_top, ← mem_trivial],
  end }

instance dense.grothendieck : grothendieck (dense C) :=
{ max := λ X Y f, ⟨Y, 𝟙 Y, ⟨⟩⟩,
  stab :=
    begin
      intros X Y S H h Z f,
      rcases H (f ≫ h) with ⟨W, g, H⟩,
      refine ⟨W, g, _⟩,
      simpa,
    end,
  trans :=
    begin
      intros X S H₁ R H₂ Y f,
      rcases H₁ f with ⟨Z,g,H₃⟩,
      rcases H₂ _ H₃ (𝟙 Z) with ⟨W,h,H₄⟩,
      refine ⟨W, (h ≫ 𝟙 Z ≫ g), _⟩,
      simpa using H₄,
    end }

/--
A category satisfies the right Ore condition if any span can be completed to a
commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition.
-/
def right_ore_condition (C : Type u) [category.{v} C] : Prop :=
∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ W (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

/--
The atomic sieveset is a grothendieck topology when it satisfies the right ore condition.
-/
instance atomic.grothendieck
  (hro : right_ore_condition C)
  : grothendieck (atomic C) :=
{ max := λ X, ⟨_, 𝟙 _, ⟨⟩⟩,
  stab :=
  begin
    rintros X Y S ⟨Z, f, hf⟩ h,
    rcases hro h f with ⟨W, g, k, comm⟩,
    refine ⟨_, g, _⟩,
    simp [mem_pullback, comm, hf],
  end,
  trans :=
  begin
    rintros X S ⟨Y, f, hf⟩ R h,
    rcases h f hf with ⟨Z, g, hg⟩,
    exact ⟨_, _, hg⟩,
  end }

open opposite

def matching_family (P : Cᵒᵖ ⥤ Type v) (S : sieve X) :=
S.functor ⟶ P

def amalgamation {P : Cᵒᵖ ⥤ Type v} {S : sieve X} (γ : matching_family P S) :=
{α : yoneda.obj X ⟶ P // sieve.functor_inclusion S ≫ α = γ}

@[derive subsingleton]
def sheaf_condition (J : sieve_set C) [grothendieck J] (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
Π (X : C) (S : sieve X) (γ : matching_family P S), S ∈ J X → unique (amalgamation γ)

def matching_family' (P : Cᵒᵖ ⥤ Type v) {c : C} (S : sieve c) :=
{x : Π {d : C} {f : d ⟶ c}, S.arrows f → P.obj (opposite.op d) //
 ∀ {d e : C} (f : d ⟶ c) (g : e ⟶ d) (h : S.arrows f), x (S.downward_closed h g) = P.map g.op (x h)}

def amalgamation' {P : Cᵒᵖ ⥤ Type v} {c : C} {S : sieve c} (γ : matching_family' P S) :=
{y : P.obj (opposite.op c) // ∀ {d : C} (f : d ⟶ c) (hf : S.arrows f), P.map f.op y = γ.1 hf}

@[derive subsingleton]
def sheaf_condition' (J : sieve_set C) [grothendieck J] (P : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
Π (c : C) (S : sieve c) (γ : matching_family' P S), S ∈ J c → unique (amalgamation' γ)

def matching_family'_equiv_matching_family (P : Cᵒᵖ ⥤ Type v) : matching_family' P S ≃ matching_family P S :=
{ to_fun := λ x, ⟨λ _ t, x.1 t.2, λ c c' f, funext $ λ t, x.2 _ _ t.2⟩,
  inv_fun := λ x, ⟨λ d f hf, x.app _ ⟨f, hf⟩, λ d d' f g h, congr_fun (x.2 g.op) ⟨f, h⟩⟩,
  left_inv := λ _, subtype.ext $ funext $ λ _, funext $ λ _, funext $ λ _, rfl,
  right_inv := λ _, by { ext _ ⟨_, _⟩, refl } }

def amalgamation'_equiv_amalgamation (P : Cᵒᵖ ⥤ Type v) (x : matching_family' P S) :
  amalgamation (matching_family'_equiv_matching_family P x) ≃ (amalgamation' x) :=
{ to_fun := λ γ,
  { val := γ.1.app _ (𝟙 X),
    property := λ d f hf,
    begin
      have := congr_fun (γ.1.naturality f.op) (𝟙 _),
      dsimp at this,
      erw ← this,
      rw comp_id,
      have q := congr_arg (λ t, nat_trans.app t (opposite.op d)) γ.2,
      dsimp at q,
      have := congr_fun q ⟨f, hf⟩,
      exact this,
    end },
  inv_fun := λ γ,
  { val :=
    { app := λ c f, P.map f.op γ.1,
      naturality' := λ c c' f, funext $ λ g,
      begin
        dsimp at g,
        dsimp,
        rw P.map_comp,
        refl,
      end },
    property :=
    begin
      ext c ⟨f, hf⟩,
      apply γ.2,
    end },
  left_inv :=
  begin
    rintro ⟨γ₁, γ₂⟩,
    ext d f,
    dsimp,
    dsimp at f,
    have := congr_fun (γ₁.naturality f.op) (𝟙 X),
    dsimp at this,
    rw [← this, comp_id],
  end,
  right_inv :=
  begin
    rintro ⟨γ₁, γ₂⟩,
    ext1,
    dsimp,
    rw P.map_id,
    refl,
  end }

def sheaf'_equiv_sheaf (J : sieve_set C) [grothendieck J] (P : Cᵒᵖ ⥤ Type v) :
  sheaf_condition J P ≅ sheaf_condition' J P :=
{ hom :=
  begin
    intros h c S γ hS,
    apply equiv.unique (amalgamation'_equiv_amalgamation _ _).symm,
    apply h _ _ _ hS,
  end,
  inv :=
  begin
    intros h c S γ hS,
    haveI := h _ _ ((matching_family'_equiv_matching_family P).symm γ) hS,
    have := equiv.unique (amalgamation'_equiv_amalgamation P ((matching_family'_equiv_matching_family P).symm γ)),
    simpa using this,
  end }

end grothendieck

end category_theory
