import linear_algebra.tensor_product m4r.projective_resolution

universe u
variables {R : Type u} [comm_ring R] {A B C : Type u} [add_comm_group A]
  [add_comm_group B] [add_comm_group C] [module R A] [module R B] [module R C]
  {A' B' C' : Type u} [add_comm_group A']
  [add_comm_group B'] [add_comm_group C'] [module R A'] [module R B'] [module R C']
set_option old_structure_cmd true

structure is_short_mid_exact
  (f : A →ₗ[R] B) (g : B →ₗ[R] C) :=
(exact : g.ker = f.range)

structure is_short_left_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) extends is_short_mid_exact f g :=
(inj : function.injective f)

structure is_short_right_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) extends is_short_mid_exact f g :=
(surj : function.surjective g)

structure is_short_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) extends
  is_short_left_exact f g, is_short_right_exact f g

instance is_short_exact.subsingleton (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
  subsingleton (is_short_exact f g) :=
⟨λ a b, by cases a; cases b; refl⟩

def is_left_exact_of_postcomp (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_exact f g)
  (N : Type u) [add_comm_group N] [module R N] :
  is_short_left_exact (linear_map.llcomp R N _ _ f) (linear_map.llcomp R N _ _ g) :=
sorry

def is_left_exact_of_precomp (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_exact f g)
  {N : Type u} [add_comm_group N] [module R N] :
  is_short_left_exact (g.lcomp R N) (f.lcomp R N) :=
sorry

def is_right_exact_of_tensor (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_exact f g)
  {N : Type u} [add_comm_group N] [module R N] :
  is_short_right_exact (f.ltensor N) (g.ltensor N) :=
sorry

def to_chain_complex_X (f : A →ₗ[R] B) (g : B →ₗ[R] C) : ℤ → Module R
| 0 := Module.of R C
| 1 := Module.of R B
| 2 := Module.of R A
| (int.of_nat (m+3)) := 0
| -[1+ m] := 0

def to_chain_complex_d (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
  Π n : ℤ, to_chain_complex_X f g (succ n) ⟶ to_chain_complex_X f g n
| 0 := g
| 1 := f
| (int.of_nat (m+2)) := 0
| -[1+ m] := 0

def to_chain_complex_d_squared (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : ∀ x, g (f x) = 0) :
  Π n : ℤ, to_chain_complex_d f g (succ n) ≫ to_chain_complex_d f g n = 0
| 0 := linear_map.ext h
| 1 := linear_map.comp_zero _
| (int.of_nat (m+2)) := linear_map.comp_zero _
| -[1+ m] := linear_map.zero_comp _

def to_chain_complex (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : ∀ x, g (f x) = 0) :
  chain_complex ℤ (Module R) :=
chain_complex.mk' (to_chain_complex_X f g) (to_chain_complex_d f g)
(to_chain_complex_d_squared f g h)

def to_cochain_complex_X (f : A →ₗ[R] B) (g : B →ₗ[R] C) : ℤ → Module R
| 0 := Module.of R A
| 1 := Module.of R B
| 2 := Module.of R C
| (int.of_nat (m+3)) := 0
| -[1+ m] := 0

def to_cochain_complex_d (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
  Π n : ℤ, to_cochain_complex_X f g n ⟶ to_cochain_complex_X f g (succ n)
| 0 := f
| 1 := g
| (int.of_nat (m+2)) := 0
| -[1+ m] := 0

def to_cochain_complex_d_squared (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : ∀ x, g (f x) = 0) :
  Π n : ℤ, to_cochain_complex_d f g n ≫ to_cochain_complex_d f g (succ n) = 0
| 0 := linear_map.ext h
| 1 := linear_map.zero_comp _
| (int.of_nat (m+2)) := linear_map.comp_zero _
| -[1+ m] := linear_map.comp_zero _

def to_cochain_complex (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : ∀ x, g (f x) = 0) :
  cochain_complex ℤ (Module R) :=
cochain_complex.mk' (to_cochain_complex_X f g) (to_cochain_complex_d f g)
(to_cochain_complex_d_squared f g h)

lemma d_squared_of_mid_exact {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  (h : is_short_mid_exact f g) (x) : g (f x) = 0 :=
linear_map.mem_ker.1 $ by rw h.1; exact linear_map.mem_range_self _ _
#check chain_complex ℤ (Module R)
noncomputable def d_aux (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact)) :
  (F.f 0).ker → (F.f 2).range.quotient :=
λ x, by
  {  let y := classical.some (H.2 x.1), -- let `z`y be such that `g(y) = x`
     have h1 : F.f 1 y ∈ k.ker, by -- under the map `B → B'`, `y` lands in `Ker k`
     { show (to_chain_complex j k _).d 1 0 (F.f 1 y) = 0,
       erw ←comm_apply, erw classical.some_spec (H.2 x.1),
       exact x.2 },
     let z := classical.some (submodule.le_def'.1 (le_of_eq H'.1) _ h1),
     -- let `z` be such that `j(z)` is `y`'s image in `B'.`
     exact submodule.mkq _ z -- use the class of `z` in `A'/Im(A → A')`.
     }

lemma d_well_def (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact))
  {x : (F.f 0).ker} {y v : B} (hy : g y = x.1) (hv : g v = x.1) {hyk : F.f 1 y ∈ k.ker}
  {hvk : F.f 1 v ∈ k.ker} :
  submodule.mkq (F.f 2).range (classical.some (submodule.le_def'.1 (le_of_eq H'.1) _ hyk))
  = submodule.mkq (F.f 2).range (classical.some (submodule.le_def'.1 (le_of_eq H'.1) _ hvk)) :=
quotient.sound' $ show _ - _ ∈ _,
begin
  have h1 := (classical.some_spec (submodule.le_def'.1 (le_of_eq H'.1) _ hyk)).2,
  have h2 := (classical.some_spec (submodule.le_def'.1 (le_of_eq H'.1) _ hvk)).2,
  obtain ⟨z, hz⟩ : y - v ∈ f.range := by
  { rw [←H.1, linear_map.mem_ker, g.map_sub, hy, hv, sub_self], },
  rw linear_map.mem_range,
  use [z],
  refine H'.2 _,
  rw [j.map_sub, h1, h2],
  show (to_chain_complex j k _).d 2 1 (F.f 2 z) = _,
  erw [←comm_apply, hz.2, linear_map.map_sub],
end

noncomputable def snake_d (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact)) :
  (F.f 0).ker →ₗ[R] (F.f 2).range.quotient :=
{ to_fun := d_aux f g H j k H' F,
  map_add' := sorry,
  map_smul' := sorry }

def ker_coker_complex_X {cov : bool} {F G : differential_object.complex_like ℤ (Module R) cov} (f : F ⟶ G) :
  ℤ → Module R
| 0 := Module.of R (f.f 0).range.quotient
| 1 := Module.of R (f.f 1).range.quotient
| 2 := Module.of R (f.f 2).range.quotient
| 3 := Module.of R (f.f 0).ker
| 4 := Module.of R (f.f 1).ker
| 5 := Module.of R (f.f 2).ker
| (int.of_nat (m+6)) := 0
| -[1+ m] := 0

noncomputable def ker_coker_complex_d (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact)) :
  Π n : ℤ, ker_coker_complex_X F (succ n) →ₗ[R] ker_coker_complex_X F n
| 0 := submodule.mapq _ _ k sorry
| 1 := submodule.mapq _ _ j sorry
| 2 := @snake_d R _ A B C _ _ _ _ _ _ A' B' C' _ _ _ _ _ _ f g H j k H' F
| 3 := linear_map.cod_restrict (F.f 0).ker (g.comp (F.f 1).ker.subtype) sorry
| 4 := linear_map.cod_restrict (F.f 1).ker (f.comp (F.f 2).ker.subtype) sorry
| (int.of_nat (m+5)) := 0
| -[1+ m] := 0

noncomputable def ker_coker_complex (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact)) :
  chain_complex ℤ (Module R) :=
chain_complex.mk' (ker_coker_complex_X F) (ker_coker_complex_d f g H j k H' F)
  sorry

def snake (f : A →ₗ[R] B) (g : B →ₗ[R] C) (H : is_short_right_exact f g)
  (j : A' →ₗ[R] B') (k : B' →ₗ[R] C') (H' : is_short_left_exact j k)
  (F : to_chain_complex f g (d_squared_of_mid_exact H.to_is_short_mid_exact)
     ⟶ to_chain_complex j k (d_squared_of_mid_exact H'.to_is_short_mid_exact)) (n : ℤ) :
  subsingleton (chain_complex.homology R (ker_coker_complex f g H j k H' F) n) :=
sorry

namespace differential_object.complex_like
variables {ι : Type} [has_succ ι] {cov : bool}

def is_short_exact {F G H : differential_object.complex_like ι (Module R) cov}
  (f : F ⟶ G) (g : G ⟶ H) :=
∀ n, is_short_exact (f.f n) (g.f n)

end differential_object.complex_like

def triples_succ (n : ℤ) : ℕ → ℤ × ℕ
| 0 := (n, 1)
| 1 := (n, 2)
| 2 := (n + 1, 0)
| (m+3) := triples_succ m

instance : has_succ (ℤ × ℕ) :=
⟨λ n, triples_succ n.1 n.2⟩

namespace cochain_complex
open differential_object.complex_like

def LES_obj_aux {F G H : cochain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
  ℕ → Module R
| 0 := Module.of R (cohomology R F n)
| 1 := Module.of R (cohomology R G n)
| 2 := Module.of R (cohomology R H n)
| (m+3) := LES_obj_aux m

def LES_obj {F G H : cochain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (n : ℤ × ℕ) :=
LES_obj_aux f g n.1 n.2

end cochain_complex
namespace chain_complex
open differential_object.complex_like

def to_mid_exact {F G H : chain_complex ℤ (Module R)}
  {f : F ⟶ G} {g : G ⟶ H} (Hfg : is_short_exact f g) (n : ℤ) :
  is_short_mid_exact (f.f n) (g.f n) :=
(Hfg n).to_is_short_right_exact.to_is_short_mid_exact

def triple_d_aux {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  Π m : ℤ, (to_chain_complex (f.f (n + 1)) (g.f (n + 1)) (d_squared_of_mid_exact $ to_mid_exact Hfg (n + 1))).X m
  →ₗ[R] (to_chain_complex (f.f n) (g.f n) (d_squared_of_mid_exact $ to_mid_exact Hfg n)).X m
| 0 := H.d _ _
| 1 := G.d _ _
| 2 := F.d _ _
| (int.of_nat (m+3)) := 0
| -[1+ m] := 0

def triple_d {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  to_chain_complex (f.f (n + 1)) (g.f (n + 1)) (d_squared_of_mid_exact $ to_mid_exact Hfg (n + 1))
  ⟶ to_chain_complex (f.f n) (g.f n) (d_squared_of_mid_exact $ to_mid_exact Hfg n) :=
{ f := triple_d_aux f g Hfg n,
  comm := sorry }

noncomputable def connecting {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  homology R H (n + 1) →ₗ[R] homology R F n :=
submodule.liftq _
(by { let L : (H.d _ _).ker →ₗ[R] (F.d _ _).range.quotient := snake_d (f.f (n + 1)) (g.f (n + 1))
        (Hfg (n + 1)).to_is_short_right_exact (f.f n) (g.f n) (Hfg n).to_is_short_left_exact
          (triple_d f g Hfg n),
    -- `L` is the map we get from the Snake Lemma from `Ker d(H)ₙ₊₁ → Coker d(F)ₙ`
    let L' := L.cod_restrict ((F.d _ (n - 1)).ker.map (F.d _ _).range.mkq) sorry,
    -- `L'` is `L` with a restricted codomain, so it maps into the image of `Ker d(F)ₙ₋₁` under the quotient map `Fₙ₋₁ → Coker d(Fₙ)`
    let L1 := (map_mkq_equiv_quotient_comap_subtype_equiv _ _).to_linear_map.comp L',
    -- The homology is defined as the quotient of `Ker d(F)ₙ₋₁` by the preimage of `Im d(F)ₙ` under inclusion `Ker d(F)ₙ₋₁ → Fₙ₋₁`, because `Im d(F)ₙ` has type 'submodule of `Fₙ₋₁`', not type 'submodule of `Ker d(F)ₙ₋₁`'.
    -- This obviously 'the same as' the codomain of `L'`, but not definitionally equal, so we compose with another isomorphism.
    let e : (H.d (n + 1) (n + 1 - 1)).ker ≃ₗ[R] (H.d (n + 1) n).ker :=
     chain_complex.ker_equiv_ker rfl (add_sub_cancel n 1),
    -- Finally, we compose with an isomorphism that resolves the non-definitionally equal indices `n + 1 - 1 = n.`
    exact L1.comp e.to_linear_map }) sorry

constant connecting_exact_left {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  (connecting f g Hfg n).ker = (homology_map g (n + 1)).range

constant connecting_exact_right {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  (homology_map f n).ker = (connecting f g Hfg n).range

def LES_obj_aux {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  ℕ → Module R
| 0 := Module.of R (homology R H n)
| 1 := Module.of R (homology R G n)
| 2 := Module.of R (homology R F n)
| (m+3) := LES_obj_aux m

def LES_obj {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ × ℕ) :=
LES_obj_aux f g Hfg n.1 n.2

noncomputable def LES_map_aux {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  Π m : ℕ, LES_obj f g Hfg (succ (n, m)) ⟶ LES_obj f g Hfg (n, m)
| 0 := homology_map g n
| 1 := homology_map f n
| 2 := connecting f g Hfg n
| (m+3) := LES_map_aux m

/-- We define `d` to `LES_map_aux` for `i, j` such that `j + 1 = i`, and 0 otherwise. -/
noncomputable def LES {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) :
  differential_object.complex_like (ℤ × ℕ) (Module R) ff :=
{ X := LES_obj f g Hfg,
  d := λ i j, if h : succ j = i then
  ((LES_map_aux f g Hfg j.1 j.2).comp (category_theory.eq_to_hom (congr_arg (LES_obj f g Hfg) h.symm)))
     else 0,
  d_comp_d := sorry,
  d_eq_zero := sorry }

open is_projective

-- if I have time.
/-def horseshoe_d {A B C : Type u} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  [module R A] [module R B] [module R C] (F : projective_resolution R A) (G : projective_resolution R C) :
  Π n : ℕ, F.complex.X (n + 1) × G.complex.X (n + 1) →ₗ[R] F.complex.X n × G.complex.X n
| 0 := sorry
| (n + 1) := sorry

def horseshoe {A B C : Type u} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  [module R A] [module R B] [module R C] (F : projective_resolution R A) (G : projective_resolution R C) :
  projective_resolution R B :=
{ complex :=
  { X := λ n, Module.of R (F.complex.X n × G.complex.X n),
    d := _,
    d_comp_d := _,
    d_eq_zero := _ },
  bounded := _,
  projective := _,
  resolution := _ }-/

/-
def triple_homology (F : differential_object.complex_like (ℤ × ℕ) (Module R) ff) :
  ℤ → Module R := sorry

theorem LES_is_exact {F G H : chain_complex ℤ (Module R)}
  (f : F ⟶ G) (g : G ⟶ H) (Hfg : is_short_exact f g) (n : ℤ) :
  subsingleton (triple_homology (LES f g Hfg) n) := sorry-/
end chain_complex

variables (A B)

open is_projective chain_complex differential_object.complex_like

lemma is_short_exact_of_ltensor {A B C : Type u} [add_comm_group A] [module R A] [add_comm_group B] [module R B]
  [add_comm_group C] [module R C] {F : projective_resolution R A} {G : projective_resolution R B}
  {H : projective_resolution R C} (f : F.complex ⟶ G.complex) (g : G.complex ⟶ H.complex)
  (Hfg : is_short_exact f g) (M : Module.{u} R) :
  is_short_exact (ltensor R M f) (ltensor R M g) := sorry

def Tor {A : Type u} [add_comm_group A] [module R A]
  (P : projective_resolution R A) (n : ℕ) :=
homology R (P.complex.tensor_pure R (Module.of R B)) n

noncomputable def Tor_LES {A B C : Type u} [add_comm_group A] [module R A] [add_comm_group B] [module R B]
  [add_comm_group C] [module R C] (F : projective_resolution R A) (G : projective_resolution R B)
  (H : projective_resolution R C) (f : F.complex ⟶ G.complex) (g : G.complex ⟶ H.complex)
  (Hfg : is_short_exact f g) (M : Module.{u} R) :=
  LES (ltensor R M f) (ltensor R M g) (is_short_exact_of_ltensor f g Hfg M)

def Ext (P : projective_resolution R A) (n : ℕ) :=
cochain_complex.cohomology R (P.complex.hom_fst R (Module.of R B)) n
