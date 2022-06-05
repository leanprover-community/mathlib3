
import representation_theory.invariants
import representation_theory.cohomology.shenyang
import linear_algebra.quotient
universes v u

variables {k : Type*} [comm_ring k] {G : Type*} [group G] {V : Type*}
  [add_comm_group V] [module k V] (ρ : representation k G V)
noncomputable theory

lemma stupid_lemma (a b c : V) :
  a - b + c = 0 ↔ b = a + c :=
by rw [sub_add_eq_add_sub, sub_eq_zero]; exact ⟨eq.symm, eq.symm⟩

def one_cocycles : submodule k (G → V) :=
{ carrier := { f | ∀ g h, f (g * h) = ρ g (f h) + f g },
  add_mem' := λ a b ha hb g h, by {simp only [pi.add_apply, ha g, hb g, (ρ g).map_add], abel},
  zero_mem' := λ g h, by simp,
  smul_mem' := λ r f hf g h, by simp [hf g] }

variables {ρ}

lemma mem_one_cocycles (f : G → V) :
  f ∈ one_cocycles ρ ↔ ∀ g h : G, f (g * h) = ρ g (f h) + f g := iff.rfl

lemma one_cocycles_map_mul (f : one_cocycles ρ) (g h : G) :
  (f : G → V) (g * h) = ρ g ((f : G → V) h) + (f : G → V) g := f.2 g h

lemma one_cocycles_cond (f : one_cocycles ρ) (g h : G) :
  ρ g ((f : G → V) h) = (f : G → V) (g * h) - (f : G → V) g :=
eq_sub_iff_add_eq.2 (one_cocycles_map_mul f g h).symm

lemma one_cocycles_cond' (f : one_cocycles ρ) (g h : G) :
  (f : G → V) g = (f : G → V) (g * h) - ρ g ((f : G → V) h) :=
eq_sub_iff_add_eq'.2 (one_cocycles_map_mul f g h).symm

lemma one_cocycles_alt_sum (f : one_cocycles ρ) (g h : G) :
  ρ g ((f : G → V) h) - (f : G → V) (g * h) + (f : G → V) g = 0 :=
by rw one_cocycles_map_mul f; abel

lemma one_cocycles_map_one (f : one_cocycles ρ) : (f : G → V) 1 = 0 :=
by have := one_cocycles_map_mul f 1 1; simp * at *

lemma one_cocycles_map_inv (f : one_cocycles ρ) (g : G) :
  ρ g ((f : G → V) g⁻¹) = -(f : G → V) g :=
by rw [←add_eq_zero_iff_eq_neg, ←one_cocycles_map_one f, ←mul_inv_self g, one_cocycles_map_mul]

lemma mem_ker_iff_mem_one_cocycles (f : (fin 1 → G) → V) :
  f ∈ (cochain.d ρ 1).ker ↔ (λ (g : G), f (λ i, g)) ∈ one_cocycles ρ :=
⟨λ hf' g h, by
  { rw ←stupid_lemma,
    have hf : cochain.d ρ 1 f (fin.cons g (λ y, h)) = 0 :=
      congr_fun (linear_map.mem_ker.1 hf') (fin.cons g (λ y, h)),
    rwa cochain.d_one_apply at hf },
λ hf, linear_map.mem_ker.2 $
  begin
    ext,
    rw [cochain.d_one_apply, pi.zero_apply, stupid_lemma],
    exact hf _ _,
  end⟩

lemma mem_one_cocycles_iff_mem_ker (f : G → V) :
  f ∈ one_cocycles ρ ↔ (λ (i : fin 1 → G), f (i 0)) ∈ (cochain.d ρ 1).ker :=
by convert (mem_ker_iff_mem_one_cocycles (λ (i : fin 1 → G), f (i 0))).symm

variables (ρ)

def ker_equiv_one_cocycles :
  (cochain.d ρ 1).ker ≃ₗ[k] one_cocycles ρ :=
let E := linear_equiv.fun_congr_left k V (equiv.fun_unique (fin 1) G) in
{ inv_fun := (E.to_linear_map.comp (one_cocycles ρ).subtype).cod_restrict
  _ (by rintros ⟨f, hf⟩; exact (mem_one_cocycles_iff_mem_ker f).1 hf),
  left_inv := λ x, by {ext, dsimp, congr, ext i, rw subsingleton.elim 0 i },
  right_inv := λ x, subtype.ext $ E.symm_apply_eq.2 $ rfl,
  ..(E.symm.to_linear_map.comp (cochain.d ρ 1).ker.subtype).cod_restrict _
  (by rintros ⟨f, hf⟩; exact (mem_ker_iff_mem_one_cocycles f).1 hf) }

def one_coboundaries : submodule k (G → V) :=
{ carrier := { f | ∃ (m : V), ∀ g : G, f g = ρ g m - m },
  zero_mem' := ⟨0, λ g, by simp⟩,
  add_mem' := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, λ g,
  begin
    dsimp,
    rw [hm g, hn g, map_add],
    abel,
  end⟩,
  smul_mem' := λ r x ⟨m, hm⟩, ⟨r • m, λ g, by simp [hm g, smul_sub]⟩ }

variables {ρ}

lemma mem_one_coboundaries (f : G → V) :
  f ∈ one_coboundaries ρ ↔ ∃ (m : V), ∀ g : G, f g = ρ g m - m := iff.rfl

lemma one_coboundaries_le_one_cocycles :
  one_coboundaries ρ ≤ one_cocycles ρ :=
λ x ⟨m, hm⟩ g h, by simp [hm, map_mul]

lemma one_coboundaries_mk_apply (f : G → V) (m : V) (hm : ∀ g : G, f g = ρ g m - m) (g : G) :
  ((⟨f, m, hm⟩ : one_coboundaries ρ) : G → V) g = f g := rfl

lemma mem_one_cocycles_of_mem_one_coboundaries (f : one_coboundaries ρ) :
  (f : G → V) ∈ one_cocycles ρ :=
λ g h, by rcases f with ⟨f, m, hf⟩; { dsimp,
  simp only [hf, ρ.map_mul, (ρ g).map_sub], abel, }

lemma mem_range_iff_mem_one_coboundaries (f : (fin 1 → G) → V) :
  f ∈ (cochain.d ρ 0).range ↔ (λ g : G, f (λ i, g)) ∈ one_coboundaries ρ :=
⟨λ ⟨x, hx⟩, ⟨x default, λ g, by convert (cochain.d_zero_apply x (λ i, g)); rw ←hx⟩,
λ ⟨m, hm⟩, ⟨λ i, m,
begin
  ext,
  rw [cochain.d_zero_apply, ←hm (x 0)],
  dsimp,
  congr,
  ext y,
  rw subsingleton.elim 0 y,
end⟩⟩

lemma mem_one_coboundaries_iff_mem_range (f : G → V) :
  f ∈ one_coboundaries ρ ↔ (λ i : fin 1 → G, f (i 0)) ∈ (cochain.d ρ 0).range :=
by convert (mem_range_iff_mem_one_coboundaries (λ i : fin 1 → G, f (i 0))).symm

variables (ρ)

def range_equiv_one_coboundaries :
  (cochain.d ρ 0).range ≃ₗ[k] one_coboundaries ρ :=
let E := linear_equiv.fun_congr_left k V (equiv.fun_unique (fin 1) G) in
{ inv_fun := (E.to_linear_map.comp (one_coboundaries ρ).subtype).cod_restrict _
  (by rintros ⟨f, hf⟩; exact (mem_one_coboundaries_iff_mem_range f).1 hf),
  left_inv := λ x, by {ext, dsimp, congr, ext i, rw subsingleton.elim 0 i },
  right_inv := λ x, by ext; refl,
  ..(E.symm.to_linear_map.comp (cochain.d ρ 0).range.subtype).cod_restrict
    _ (by rintros ⟨f, hf⟩; exact (mem_range_iff_mem_one_coboundaries f).1 hf) }

open category_theory category_theory.limits

def homology_of_rel {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  {ι : Type*} {c : complex_shape ι} (C : homological_complex V c)
  {i j k : ι} (hij : c.rel i j) (hjk : c.rel j k) :
  C.homology j ≅ homology (C.d i j) (C.d j k) (C.d_comp_d i j k) :=
homology.map_iso _ _ (arrow.iso_mk (C.X_prev_iso hij) (iso.refl _)
(by simp only [C.d_to_eq hij, arrow.mk_hom]; dsimp; rw category.comp_id))
  (arrow.iso_mk (iso.refl _) (C.X_next_iso hjk)
  (by simp [C.d_from_eq hjk])) (by dsimp; refl)

-- dunno why I can't find this or the quickest way to get it
def equiv_quotient_of_equiv {M : Type*} {N : Type*}
  [add_comm_group M] [add_comm_group N]
  [module k M] [module k N]
  (e : M ≃ₗ[k] N) (A : submodule k M) (B : submodule k N)
  (h : A.map e.to_linear_map = B) :
  (M ⧸ A) ≃ₗ[k] N ⧸ B :=
{ inv_fun := (B.mapq A e.symm.to_linear_map $ λ x hx,
  show e.symm.to_linear_map x ∈ A,
  begin
    rw ←h at hx,
    rcases hx with ⟨y, hym, hy⟩,
    erw [←hy, e.symm_apply_apply],
    exact hym
  end),
  left_inv := λ y, quotient.induction_on' y $ λ x,
    by dsimp; sorry,--rw [quotient_group.map_coe, quotient_group.map_coe];
    --exact congr_arg _ (e.symm_apply_apply x),
  right_inv := λ y, sorry, /-quotient_group.induction_on' y $ λ x,
    by dsimp; rw [quotient_group.map_coe, quotient_group.map_coe];
    exact congr_arg _ (e.apply_symm_apply x),-/
  ..(A.mapq B e.to_linear_map
  $ λ x hx, show e x ∈ B, by rw ←h; exact submodule.apply_coe_mem_map e.to_linear_map ⟨x, hx⟩) }

variables (ρ)

abbreviation firstcoh :=
one_cocycles ρ ⧸ ((one_coboundaries ρ).comap (one_cocycles ρ).subtype)

def first_iso : (cochain_cx ρ).homology 1 ≃ₗ[k] firstcoh ρ :=
((homology_of_rel (cochain_cx ρ) (show 0 + 1 = 1, from rfl)
  (show 1 + 1 = 2, from rfl)).trans
  (Module.cokernel_iso_range_quotient _)).to_linear_equiv.trans $
  equiv_quotient_of_equiv
  (((kernel_subobject_iso _).trans $
    Module.kernel_iso_ker _).to_linear_equiv.trans $
  ker_equiv_one_cocycles ρ) _ _ $
begin
  ext,
  split,
  { rintros ⟨z, ⟨y, hy⟩, hz⟩,
    rw submodule.mem_comap,
    sorry
   },
  { sorry },
end
