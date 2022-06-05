import representation_theory.invariants
import representation_theory.cohomology.shenyang
import representation_theory.cohomology.op_complex

universes v u w

noncomputable theory
open representation
section gotuniverses

variables {k : Type u} [comm_ring k] {G : Type u} [group G] {V : Type v}
  [add_comm_group V] [module k V] (ρ : representation k G V)

-- not sure this should exist because ... universes.. somehow
instance fucksake (M : Rep k G) : has_coe (invariants M.ρ) M :=
⟨λ x, x.1⟩
/-lemma representation.comm {M N : Type u} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] {ρM : representation k G M} {ρN : representation k G N}
  (f : Rep.of ρM ⟶ Rep.of ρN) (g : G) (x : M) :
  f.hom (ρM g x) = ρN g (f.hom x) :=
linear_map.ext_iff.1 (f.comm _) _-/

lemma Rep.comm_apply {M N : Rep k G} (f : M ⟶ N) (g : G) (x : M) :
  f.hom ((M.ρ g).as_hom x) = (N.ρ g).as_hom (f.hom x) :=
linear_map.ext_iff.1 (f.comm _) _

lemma Rep.mem_invariants {M : Rep k G} (x : M) :
  x ∈ invariants M.ρ ↔ ∀ g : G, (M.ρ g).as_hom x = x := iff.rfl

def invariants_map {M N : Rep k G} (f : M ⟶ N) :
  invariants M.ρ →ₗ[k] invariants N.ρ :=
(f.hom.comp (invariants M.ρ).subtype).cod_restrict _
  (λ x g, by { erw ←Rep.comm_apply, congr, exact (Rep.mem_invariants (x : M)).1 x.2 _ })

lemma invariants_map_apply {M N : Rep k G} (f : M ⟶ N) (x : invariants M.ρ) :
  (invariants_map f x : N) = f.hom (x : M) :=
rfl

open category_theory category_theory.limits

open_locale zero_object

def cochain_complex.zeroth {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : cochain_complex V ℕ) :
  C.homology 0 ≅ homology (0 : 0 ⟶ C.X 0) (C.d 0 1) zero_comp :=
homology.map_iso _ zero_comp
 (arrow.iso_mk (C.X_prev_iso_zero cochain_complex.prev_nat_zero) (iso.refl _)
   (by { simp only [cochain_complex.prev_nat_zero, homological_complex.d_to_eq_zero,
     zero_comp, exact.w, arrow.mk_hom, comp_zero]}))
 (arrow.iso_mk (iso.refl _) (C.X_next_iso rfl) (by {simp only [iso.refl_hom, arrow.mk_hom,
   category.id_comp, homological_complex.d_from_comp_X_next_iso] }))
  (by { simp only [iso.refl_hom, arrow.iso_mk_hom_left, arrow.iso_mk_hom_right], refl })

def cochain_complex.Module_zeroth_iso_ker {R : Type*} [ring R] (C : cochain_complex (Module R) ℕ) :
  C.homology 0 ≅ Module.of R (C.d 0 1).ker :=
(C.zeroth.trans (homology_of_zero_left _)).trans
  ((kernel_subobject_iso _).trans (Module.kernel_iso_ker _))

end gotuniverses

section

variables {k : Type*} [comm_ring k] {G : Type*} [group G] {V : Type*}
  [add_comm_group V] [module k V] (ρ : representation k G V)

-- whyyyyys this slow. theres no category shit

abbreviation ker_to_invariants : (cochain.d ρ 0).ker →ₗ[k] invariants ρ :=
((linear_equiv.fun_unique (fin 0 → G) k V).to_linear_map.comp
    (cochain.d ρ 0).ker.subtype).cod_restrict _
  (begin
    rintros ⟨x, h'⟩ g,
    have h : cochain.d ρ 0 x (λ y : fin 1, g) = 0 :=
      congr_fun (linear_map.mem_ker.1 h') (λ y : fin 1, g),
    rwa [cochain.d_zero_apply, sub_eq_zero] at h,
  end)

abbreviation invariants_to_ker : invariants ρ →ₗ[k] (cochain.d ρ 0).ker :=
((linear_equiv.fun_unique (fin 0 → G) k V).symm.to_linear_map.comp
    (invariants ρ).subtype).cod_restrict _ $ λ x, linear_map.mem_ker.2 $
  (begin
    ext f,
    rw cochain.d_zero_apply,
    dsimp,
    rw [(ρ.mem_invariants (x : V)).1 x.2, sub_self]
  end)

-- why so slow -______-
def ker_equiv_invariants : (cochain.d ρ 0).ker ≃ₗ[k] invariants ρ :=
{ inv_fun := invariants_to_ker ρ,
  left_inv := λ x, by {ext i, dsimp, rw subsingleton.elim default i },
  right_inv := λ x, by ext; refl,
  ..ker_to_invariants ρ }

def zeroth : (cochain_cx ρ).homology 0 ≃ₗ[k] invariants ρ :=
(cochain_complex.Module_zeroth_iso_ker _).to_linear_equiv.trans
  (ker_equiv_invariants ρ)


end
