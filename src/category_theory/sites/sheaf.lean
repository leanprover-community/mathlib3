import Kenny.sites.lattice

universes v w u

namespace category_theory

def presheaf (C : Type u) [category.{v} C] : Type (max u v (w+1)) :=
Cᵒᵖ ⥤ Type w

namespace presheaf

variables {C : Type u} [category.{v} C] (F : presheaf.{v w} C)

def eval (U : C) : Type w :=
F.1 (op U)

def res {U V : C} (f : U ⟶ V) : F.eval V → F.eval U :=
F.2 (has_hom.hom.op f)

@[simp] lemma res_id (U : C) (s : F.eval U) : F.res (𝟙 U) s = s :=
congr_fun (F.map_id (op U)) s

@[simp] lemma res_res (U V W : C) (f : W ⟶ V) (g : V ⟶ U) (s : F.eval U) :
  F.res f (F.res g s) = F.res (f ≫ g) s :=
(congr_fun (F.map_comp (has_hom.hom.op g) (has_hom.hom.op f)) s).symm

end presheaf

structure sheaf (C : Type u) [category.{v} C] [has_pullback C] [has_site.{v} C] : Type (max u v (w+1)) :=
(to_presheaf : presheaf.{v w} C)
(ext : ∀ U : C, ∀ s t : to_presheaf.eval U, ∀ c ∈ has_site.cov U,
  (∀ d : Σ V, V ⟶ U, d ∈ c → to_presheaf.res d.2 s = to_presheaf.res d.2 t) →
  s = t)
(glue : ∀ U : C, ∀ c ∈ has_site.cov U, ∀ F : Π d : Σ V, V ⟶ U, d ∈ c → to_presheaf.eval d.1,
  (∀ d1 d2 : Σ V, V ⟶ U, ∀ H1 : d1 ∈ c, ∀ H2 : d2 ∈ c,
    to_presheaf.res (pullback.fst d1.2 d2.2) (F d1 H1) =
    to_presheaf.res (@@pullback.snd _ _inst_2 d1.2 d2.2) (F d2 H2)) →
  ∃ g : to_presheaf.eval U, ∀ d : Σ V, V ⟶ U, ∀ H : d ∈ c,
    to_presheaf.res d.2 g = F d H)

end category_theory
