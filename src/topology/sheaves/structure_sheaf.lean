import algebraic_geometry.prime_spectrum
import ring_theory.localization
import algebra.category.CommRing
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.bundled_subring

universe u

noncomputable theory

variables (R : Type u) [comm_ring R]

open Top
open topological_space
open category_theory
open opposite

@[reducible]
def stalks := λ (P : Top.of (prime_spectrum R)), localization.at_prime P.as_ideal

variables {R}

/--
Quoting Hartshorne:

For an open set $$U ⊆ Spec A$$, we define $$𝒪(U)$$ to be the set of functions
$$s : U → \bigsqcup_{𝔭 ∈ U} A_𝔭$$, such that $s(𝔭) ∈ A_𝔭$$ for each $$𝔭$$,
and such that $$s$$ is locally a quotient of elements of $$A$$:
to be precise, we require that for each $$𝔭 ∈ U$$, there is a neighborhood $$V$$ of $$𝔭$$,
contained in $$U$$, and elements $$a, f ∈ A$$, such that for each $$𝔮 ∈ V, f ∉ 𝔮$$,
and $$s(𝔮) = a/f$$ in $$A_𝔮$$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, stalks x`.
-/
def locally_fraction {U : opens (Top.of (prime_spectrum R))} (f : Π x : U, stalks R x) : Prop :=
∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r

variables (R)

/--
We verify that `locally_fraction` is a `local_predicate`.
This is purely formal, just shuffling around quantifiers.
-/
def locally_fraction_local : local_predicate (stalks R) :=
{ pred := λ U f, locally_fraction f,
  res := λ V U i f h x,
  begin
    rcases h (i x : U) with ⟨W, m, i, r, s, w⟩,
    exact ⟨V ⊓ W, ⟨x.2, m⟩, opens.inf_le_left V W, r, s, (λ y, w ⟨y.1, y.2.2⟩)⟩,
  end,
  locality := λ U f w x,
  begin
    rcases w x with ⟨V, m, i, h⟩, clear w,
    rcases h ⟨x.1, m⟩ with ⟨V', m', i', r, s, h'⟩, clear h,
    exact ⟨V', m', i' ≫ i, r, s, h'⟩,
  end, }

def structure_sheaf_in_Type : sheaf (Type u) (Top.of (prime_spectrum R)) :=
subsheaf_to_Types (locally_fraction_local R)

def sections_subring (U : (opens (Top.of (prime_spectrum R)))ᵒᵖ) :
  subring (Π x : unop U, stalks R x) :=
{ carrier := { f | locally_fraction f },
  zero_mem' :=
  begin
    intro x,
    use unop U,
    fsplit,
    exact x.2,
    use 𝟙 _,
    use 0,
    use 1,
    intro y,
    fsplit,
    { rw ←ideal.ne_top_iff_one, exact y.1.as_ideal_is_prime.1, },
    { simp, },
  end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    use Va ⊓ Vb,
    fsplit, exact ⟨ma, mb⟩,
    use opens.inf_le_left _ _ ≫ ia,
    use ra * sb + rb * sa,
    use sa * sb,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩,
    fsplit,
    { sorry, },
    { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
      erw [←wa, ←wb],
      simp only [mul_assoc],
      congr' 2,
      rw [mul_comm], refl, }
  end,
  neg_mem' := sorry,
  one_mem' := sorry,
  mul_mem' := sorry, }

-- TODO: we need to prove that the stalk at `P` is `localization.at_prime P.as_ideal`

instance blah (U : (opens (Top.of (prime_spectrum R)))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type R).presheaf.obj U) :=
(sections_subring R U).to_comm_ring

@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (Top.of (prime_spectrum R)) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type R).presheaf.obj U),
  map := λ U V i, sorry, }

/--
Just some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing R ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type R).presheaf :=
nat_iso.of_components
  (λ U, iso.refl _)
  (λ U V i, begin dsimp, simp, sorry, end)

/--
The structure sheaf on $$Spec R$$.
-/
def structure_sheaf : sheaf CommRing (Top.of (prime_spectrum R)) :=
{ presheaf := structure_presheaf_in_CommRing R,
  sheaf_condition :=
    -- We check the sheaf condition under `forget CommRing`.
    (sheaf_condition_equiv_sheaf_condition_comp _ _).symm
      (sheaf_condition_equiv_of_iso (structure_presheaf_comp_forget R).symm
        (structure_sheaf_in_Type R).sheaf_condition), }
