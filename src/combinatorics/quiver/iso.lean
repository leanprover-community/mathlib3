import combinatorics.quiver.basic

universes u v w z

namespace quiver

structure iso (U V : Type*) [quiver.{u+1} U] [quiver.{v+1} V] extends prefunctor U V :=
(inv_prefunctor : V ⥤q U)
(left_inv : to_prefunctor ⋙q inv_prefunctor = 𝟭q _)
(right_inv : inv_prefunctor ⋙q to_prefunctor = 𝟭q _)

infix ` ≃q `:60 := iso

variables {U V W Z : Type*} [quiver.{u+1} U] [quiver.{v+1} V] [quiver.{w+1} W] [quiver.{z+1} Z]

instance : has_coe (iso U V) (prefunctor U V) :=
⟨iso.to_prefunctor⟩


def iso.refl (U : Type*) [quiver.{u+1} U] : iso U U := ⟨𝟭q _, 𝟭q _, rfl, rfl⟩

def iso.symm (φ : iso U V) : iso V U :=
⟨φ.inv_prefunctor, φ.to_prefunctor, φ.right_inv, φ.left_inv⟩

def iso.trans (φ : iso U V) (ψ : iso V W) : iso U W :=
{ to_prefunctor := φ.to_prefunctor ⋙q ψ.to_prefunctor,
  inv_prefunctor := ψ.inv_prefunctor ⋙q φ.inv_prefunctor,
  left_inv := by
  { rw [←prefunctor.comp_assoc, prefunctor.comp_assoc φ.to_prefunctor,
        ψ.left_inv, prefunctor.comp_id, φ.left_inv], },
  right_inv := by
  { rw [←prefunctor.comp_assoc, prefunctor.comp_assoc ψ.inv_prefunctor,
        φ.right_inv, prefunctor.comp_id, ψ.right_inv], }, }

noncomputable def iso.of_bijective (φ : U ⥤q V) (hφobj : function.bijective φ.obj)
  (hφmap : ∀ (x y : U), function.bijective (φ.map : (x ⟶ y) → (φ.obj x ⟶ φ.obj y)) ) :
  iso U V :=
{ to_prefunctor := φ,
  inv_prefunctor :=
  { obj := function.surj_inv hφobj.surjective,
    map := λ (x y : V) (e : x ⟶ y), by
    { rw [←function.right_inverse_surj_inv hφobj.2 x,
          ←function.right_inverse_surj_inv hφobj.2 y] at e,
      exact ((hφmap _ _).2 e).some,  } },
  left_inv := by {
    fapply prefunctor.ext,
    { rintro x,
      simp only [function.left_inverse_surj_inv hφobj x, prefunctor.comp_obj,
                 prefunctor.id_obj, id.def], },
    { rintro x y e,
      simp, sorry, }, },
  right_inv := by {
    fapply prefunctor.ext,
    { rintro x,
      simp only [function.right_inverse_surj_inv hφobj.2 x, prefunctor.comp_obj,
                 prefunctor.id_obj, id.def], },
    { rintro x y e,
      simp, sorry, }, }, }

@[ext]
lemma iso.ext (φ ψ : iso U V) : φ = ψ ↔ φ.to_prefunctor = ψ.to_prefunctor := sorry




end quiver
