/-
2020. No rights reserved. https://unlicense.org/
Authors: Johan Commelin
-/

import ring_theory.witt_vector_preps
import tactic

noncomputable theory
open mv_polynomial

structure witt_package :=
(enum : Type)
(witt_polynomial : enum → mv_polynomial enum ℤ)
(witt_structure  : Π {idx : Type} (Φ : mv_polynomial idx ℤ), enum → mv_polynomial (idx × enum) ℤ)
(structure_prop  : ∀ {idx : Type} (Φ : mv_polynomial idx ℤ) (n : enum),
                    aeval (λ k, (witt_structure Φ k)) (witt_polynomial n) =
                    aeval (λ i, (rename_hom (λ k, (i,k)) (witt_polynomial n))) Φ)
(loc : Type)
[loc_comm_ring : comm_ring loc]
[algebra       : algebra ℤ loc]
(inj           : function.injective (algebra_map ℤ loc))
(equiv         :
begin
  let aux1 : _ := _, let aux2 : _ := _, let aux3 : _ := _,
  refine @alg_equiv loc (mv_polynomial enum loc) (mv_polynomial enum loc)
    aux1 aux2 aux2 aux3 aux3,
  swap 3, apply_instance,
  swap, apply_instance,
  convert @mv_polynomial.algebra loc enum aux1,
end)
-- (compat        :
-- begin
--   refine (equiv : mv_polynomial enum loc →ₐ[loc] mv_polynomial enum loc) = _,
--   refine aeval _,
--   intro n,
--   refine mv_polynomial.map_hom _ (witt_polynomial n),
--   refine @algebra_map ℤ loc (by apply_instance) (by apply_instance) (algebra)
-- --                   aeval (λ n, mv_polynomial.map_hom (algebra_map ℤ loc) (witt_polynomial n))
-- end)

namespace witt_package

variables (W : witt_package) (R : Type*) (S : Type*)
variables [comm_ring R] [comm_ring S]

attribute [instance] loc_comm_ring algebra

/-- The ring of Witt vectors (depending on a “Witt package” `W`). -/
def witt_vector (R : Type*) := W.enum → R

local notation `𝕎` := W.witt_vector -- type as `\bbW`

section ring_data
/-!
## Data for the ring structure

We will use the Witt package to define the data of a ring structure on the Witt vectors.
To show that this data satisfies the axioms of a ring, we will need more work,
and this will be done below.
-/

/-- An auxiliary inductive type to talk about the two sides of addition/multiplication.

`side.l` and `side.r` refer to the left and right hand sides respectively,
of expressions such as `x + y` and `x * y`.
We use this as indexing type for the Witt structure polynomials for addition and multiplication.
See `witt_add` and `witt_mul`. -/
inductive side | l | r

def side.cond {α : Type*} : side → α → α → α
| side.l x _ := x
| side.r _ y := y

open side

/-- The polynomial used for defining the element `0` of the ring of Witt vectors. -/
noncomputable def witt_zero :=
W.witt_structure (0 : mv_polynomial empty ℤ)

/-- The polynomial used for defining the element `1` of the ring of Witt vectors. -/
noncomputable def witt_one :=
W.witt_structure (1 : mv_polynomial empty ℤ)

/-- The polynomial used for defining the addition of the ring of Witt vectors. -/
noncomputable def witt_add :=
W.witt_structure (X l + X r)

/-- The polynomial used for defining the multiplication of the ring of Witt vectors. -/
noncomputable def witt_mul :=
W.witt_structure (X l * X r)

/-- The polynomial used for defining the negation of the ring of Witt vectors. -/
noncomputable def witt_neg :=
W.witt_structure (-X ())

noncomputable instance : has_zero (𝕎 R) :=
⟨λ n, aeval (λ p : empty × W.enum, p.1.elim) (W.witt_zero n)⟩

noncomputable instance : has_one (𝕎 R) :=
⟨λ n, aeval (λ p : empty × W.enum, p.1.elim) (W.witt_one n)⟩

noncomputable instance : has_add (𝕎 R) :=
⟨λ x y n, aeval (λ sn : side × W.enum, cond sn.1 (x sn.2) (y sn.2)) (W.witt_add n)⟩

noncomputable instance : has_mul (𝕎 R) :=
⟨λ x y n, aeval (λ sn : side × W.enum, cond sn.1 (x sn.2) (y sn.2)) (W.witt_mul n)⟩

noncomputable instance : has_neg (𝕎 R) :=
⟨λ x n, aeval (λ k : unit × W.enum, x k.2) (W.witt_neg n)⟩

end ring_data

section map
/-!
## Functoriality of the Witt vector construction

We define `witt_package.map`, the map between rings of Witt vectors
induced by a map between the coefficient rings.
-/

open function
variables {α : Type*} {β : Type*}

/-- The map between Witt vectors induced by a map between the coefficients. -/
def map (f : α → β) : 𝕎 α → 𝕎 β := λ w, f ∘ w

lemma map_injective (f : α → β) (hf : injective f) :
  injective (W.map f : 𝕎 α → 𝕎 β) :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_surjective (f : α → β) (hf : surjective f) :
  surjective (W.map f : 𝕎 α → 𝕎 β) :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map], rw classical.some_spec (hf (x n)) }⟩

variables (f : R →+* S)

/-- Auxiliary tactic for showing that `witt_package.map` respects ring data. -/
meta def witt_map : tactic unit :=
`[funext n,
  show f (aeval _ _) = aeval _ _,
  rw map_aeval,
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  funext p,
  rcases p with ⟨⟨⟩, i⟩; refl]

@[simp] lemma map_zero : W.map f (0 : 𝕎 R) = 0 :=
by witt_map

@[simp] lemma map_one : W.map f (1 : 𝕎 R) = 1 :=
by witt_map

@[simp] lemma map_add (x y : 𝕎 R) : W.map f (x + y) = W.map f x + W.map f y :=
by witt_map

@[simp] lemma map_mul (x y : 𝕎 R) : W.map f (x * y) = W.map f x * W.map f y :=
by witt_map

@[simp] lemma map_neg (x : 𝕎 R) : W.map f (-x) = - W.map f x :=
by witt_map

end map

section ghost_map
/-!
## Ghost map/components
-/
variables {R}
open side

noncomputable def ghost_component (n : W.enum) (x : 𝕎 R) : R :=
aeval x (W.witt_polynomial n)

noncomputable def ghost_map : 𝕎 R → (W.enum → R) := λ w n, W.ghost_component n w

@[simp] lemma ghost_map_zero : W.ghost_map (0 : 𝕎 R) = 0 :=
funext $ λ n,
begin
  have aux := (W.structure_prop (0 : mv_polynomial empty ℤ) n),
  apply_fun (aeval (λ (p : empty × W.enum), (p.1.elim : R))) at aux,
  convert aux using 1; clear aux,
  { simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
end

@[simp] lemma ghost_map_one : W.ghost_map (1 : 𝕎 R) = 1 :=
funext $ λ n,
begin
  have aux := (W.structure_prop (1 : mv_polynomial empty ℤ) n),
  apply_fun (aeval (λ (p : empty × W.enum), (p.1.elim : R))) at aux,
  convert aux using 1; clear aux,
  { simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_one, eval₂_hom_X', eval₂_hom_rename_hom],
    refl }
end

variable {R}

@[simp] lemma ghost_map_add (x y : 𝕎 R) :
  W.ghost_map (x + y) = W.ghost_map x + W.ghost_map y :=
funext $ λ n,
begin
  have aux := (W.structure_prop (X l + X r) n),
  apply_fun (aeval (λ (sn : side × W.enum), side.cond sn.1 (x sn.2) (y sn.2))) at aux,
  convert aux using 1; clear aux,
  { simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_add, eval₂_hom_X', eval₂_hom_rename_hom],
    refl }
end

@[simp] lemma ghost_map_mul (x y : 𝕎 R) :
  W.ghost_map (x * y) = W.ghost_map x * W.ghost_map y :=
funext $ λ n,
begin
  have aux := (W.structure_prop (X l * X r) n),
  apply_fun (aeval (λ (sn : side × W.enum), side.cond sn.1 (x sn.2) (y sn.2))) at aux,
  convert aux using 1; clear aux,
  { simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_mul, eval₂_hom_X', eval₂_hom_rename_hom],
    refl }
end

@[simp] lemma ghost_map_neg (x : 𝕎 R) :
  W.ghost_map (-x) = - W.ghost_map x :=
funext $ λ n,
begin
  have aux := (W.structure_prop (-X ()) n),
  apply_fun (aeval (λ (k : unit × W.enum), x k.2)) at aux,
  convert aux using 1; clear aux,
  { simp only [aeval_eq_eval₂_hom', eval₂_hom_map_hom, map_eval₂_hom],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    funext k,
    exact eval₂_hom_congr (ring_hom.ext_int _ _) rfl rfl },
  { simp only [aeval_eq_eval₂_hom', ring_hom.map_neg, eval₂_hom_X', eval₂_hom_rename_hom],
    refl }
end
.

noncomputable def ghost_map_equiv :
  𝕎 W.loc ≃ (W.enum → W.loc) :=
mv_polynomial.comap_equiv (W.equiv)

lemma ghost_map_eq :
  (W.ghost_map : 𝕎 W.loc → W.enum → W.loc) = W.ghost_map_equiv :=
begin
  ext x n,
  simp only [ghost_map_equiv, alg_equiv.coe_alg_hom, comap_apply, comap_equiv_coe],
  sorry
  -- rw aeval_X,
  -- ext w n,
  -- dsimp [ghost_map.equiv_of_invertible, witt.alg_equiv],
  -- rw [aeval_X], refl,
end

lemma ghost_map_bijective :
  function.bijective (W.ghost_map : 𝕎 W.loc → W.enum → W.loc) :=
by { rw ghost_map_eq, exact (W.ghost_map_equiv).bijective }

end ghost_map

section ring_axioms
/-! ## Verification of the ring axioms -/

variable (R)

noncomputable def comm_ring_aux₁ : comm_ring (𝕎 (mv_polynomial R W.loc)) :=
function.injective.comm_ring (W.ghost_map)
  (W.ghost_map_bijective).1
  (W.ghost_map_zero) (W.ghost_map_one) (W.ghost_map_add) (W.ghost_map_mul) (W.ghost_map_neg)

local attribute [instance] aux₁

noncomputable def aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
function.injective.comm_ring (map $ mv_polynomial.map_hom (int.cast_ring_hom ℚ))
  (map_injective _ $ mv_polynomial.coe_int_rat_map_injective _)
  (map_zero _) (map_one _) (map_add _) (map_mul _) (map_neg _)

local attribute [instance] aux₂

noncomputable instance : comm_ring (𝕎 p R) :=
function.surjective.comm_ring
  (map $ mv_polynomial.counit _) (map_surjective _ $ counit_surjective _)
  (map_zero _) (map_one _) (map_add _) (map_mul _) (map_neg _)


end ring_axioms

end witt_package
