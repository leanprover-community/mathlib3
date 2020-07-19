import category_theory.limits.shapes.kernels

open category_theory

namespace category_theory.limits

universes v u

variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

@[simps]
def cokernel_comp_is_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [has_cokernel (f ≫ g)] [has_cokernel f] [is_iso g] :
  cokernel (f ≫ g) ≅ cokernel f :=
{ hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp),
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [←category.assoc, cokernel.condition]), }

@[simps]
def cokernel_is_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [has_cokernel (f ≫ g)] [is_iso f] [has_cokernel g] :
  cokernel (f ≫ g) ≅ cokernel g :=
{ hom := cokernel.desc _ (cokernel.π g) (by simp),
  inv := cokernel.desc _ (cokernel.π (f ≫ g)) (by { rw [←cancel_epi f, ←category.assoc], simp, }), }

@[simps]
def kernel_comp_is_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [has_kernel (f ≫ g)] [has_kernel f] [is_iso g] :
  kernel (f ≫ g) ≅ kernel f :=
{ hom := kernel.lift _ (kernel.ι _) begin rw [←cancel_mono g], simp, end,
  inv := kernel.lift _ (kernel.ι _) (by simp), }

@[simps]
def kernel_is_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [has_kernel (f ≫ g)] [is_iso f] [has_kernel g] :
  kernel (f ≫ g) ≅ kernel g :=
{ hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp),
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp), }

namespace kernel_fork

variables {X Y : C} {f : X ⟶ Y}

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux (t : kernel_fork f)
  (lift : Π (s : kernel_fork f), s.X ⟶ t.X)
  (fac : ∀ (s : kernel_fork f), lift s ≫ t.ι = s.ι)
  (uniq : ∀ (s : kernel_fork f) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, by { cases j, { exact fac s, }, { simp, }, },
  uniq' := λ s m w, uniq s m (w limits.walking_parallel_pair.zero), }

/--
This is a more convenient formulation to show that a `kernel_fork` constructed using
`kernel_fork.of_ι` is a limit cone.
-/
def is_limit.of_ι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
  (lift : Π {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), W' ⟶ W)
  (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
  (uniq : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (w : m ≫ g = g'), m = lift g' eq') :
  is_limit (kernel_fork.of_ι g eq) :=
is_limit_aux _ (λ s, lift s.ι s.condition) (λ s, fac s.ι s.condition) (λ s, uniq s.ι s.condition)

end kernel_fork


namespace cokernel_cofork

variables {X Y : C} {f : X ⟶ Y}

/--
This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux (t : cokernel_cofork f)
  (desc : Π (s : cokernel_cofork f), t.X ⟶ s.X)
  (fac : ∀ (s : cokernel_cofork f), t.π ≫ desc s = s.π)
  (uniq : ∀ (s : cokernel_cofork f) (m : t.X ⟶ s.X) (w : t.π ≫ m = s.π), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, by { cases j, { simp, }, { exact fac s, }, },
  uniq' := λ s m w, uniq s m (w limits.walking_parallel_pair.one), }

/--
This is a more convenient formulation to show that a `cokernel_cofork` constructed using
`cokernel_cofork.of_π` is a limit cone.
-/
def is_colimit.of_π {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
  (desc : Π {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), Z ⟶ Z')
  (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
  (uniq : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (w : g ≫ m = g'), m = desc g' eq') :
  is_colimit (cokernel_cofork.of_π g eq) :=
is_colimit_aux _ (λ s, desc s.π s.condition) (λ s, fac s.π s.condition) (λ s, uniq s.π s.condition)

end cokernel_cofork

end category_theory.limits
