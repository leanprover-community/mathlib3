import algebra.homology2.additive

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V]

variables {c : complex_shape ι}

namespace homological_complex

section
variables [has_zero_morphisms V]

@[ext]
structure ihom (k : ℤ) (C D : homological_complex V c) :=
(hom : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.rel_step k i j → hom i j = 0 . obviously)

restate_axiom ihom.zero'
attribute [simp] ihom.zero

lemma ihom_f_injective {k : ℤ} {C₁ C₂ : homological_complex V c} :
  function.injective (λ f : ihom k C₁ C₂, ihom.hom f) :=
by tidy

namespace ihom
variables [has_zero_object V]
variables {k : ℤ} {C D : homological_complex V c}

def from_succ (f : ihom k C D) (i j : ι) : C.X_succ i ⟶ D.X j :=
match c.next i with
| none := 0
| some ⟨i',w⟩ := (C.X_succ_iso w).hom ≫ f.hom i' j
end

def to_pred (f : ihom k C D) (i j : ι) : C.X i ⟶ D.X_pred j :=
match c.prev j with
| none := 0
| some ⟨j',w⟩ := f.hom i j' ≫ (D.X_pred_iso w).inv
end

end ihom

end

section
variables [preadditive V]
variables {k : ℤ} {C D : homological_complex V c}

instance : has_zero (ihom k C D) := ⟨{ hom := λ i j, 0 }⟩
instance : has_add (ihom k C D) :=
⟨λ f g, { hom := λ i j, f.hom i j + g.hom i j, zero' := λ i j w, by simp [w] }⟩
instance : has_neg (ihom k C D) :=
⟨λ f, { hom := λ i j, -(f.hom i j), zero' := λ i j w, by simp [w] }⟩
instance : has_sub (ihom k C D) :=
⟨λ f g, { hom := λ i j, f.hom i j - g.hom i j, zero' := λ i j w, by simp [w] }⟩

instance : add_comm_group (ihom k C D) :=
function.injective.add_comm_group ihom.hom
  homological_complex.ihom_f_injective (by tidy) (by tidy) (by tidy) (by tidy)

-- def sign (k : ℤ) : ℤ := @gpow (units ℤ) _ (-1 : units ℤ) k

-- variables [has_zero_object V]

-- def δ : ihom k C D →+ ihom (k+1) C D :=
-- { to_fun := λ f,
--   { hom := λ i j, C.d_from i ≫ f.from_succ i j + (sign k) •ℤ f.to_pred i j ≫ D.d_to j,
--     zero' := begin intros, sorry, end, },
--   map_zero' := begin ext, dsimp, sorry, end,
--   map_add' := sorry, }

-- -- Now: `δ^2 = 0`
-- -- The kernel of `δ` in `ihom 0 C D` are exactly the chain maps
-- -- The preimage under `δ` of `f - g` in `ihom 1 C D` are exactly the homotopies from `f` to `g`.
-- -- There's an `eval` map `ihom k C D →+ (C.X i ⟶ D.X i.succ^k)`
-- -- ... without resorting to elements this tells you (??) that homotopic maps
-- -- induce equal maps on homology?

end

end homological_complex
