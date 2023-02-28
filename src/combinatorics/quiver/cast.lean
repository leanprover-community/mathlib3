/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.quiver.path

/-!

# Rewriting arrows and paths along vertex equalities

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files defines `hom.cast` and `path.cast` (and associated lemmas) in order to allow
rewriting arrows and paths along equalities of their endpoints.

-/

universes v v₁ v₂ u u₁ u₂

variables {U : Type*} [quiver.{u+1} U] {V : Type*} [quiver.{v+1} V]

namespace quiver

/-!
### Rewriting arrows along equalities of vertices
-/

/-- Change the endpoints of an arrow using equalities. -/
def hom.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) : u' ⟶ v' :=
eq.rec (eq.rec e hv) hu

lemma hom.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
  e.cast hu hv = cast (by rw [hu, hv]) e :=
by { subst_vars, refl }

lemma hom.cast_congr {u v u' v' : U} (hu hu' : u = u') (hv hv' : v = v') (e : u ⟶ v) :
  e.cast hu hv = e.cast hu' hv' :=
by { cases hu, cases hu', cases hv, cases hv', refl, }

lemma hom.cast_eq_iff_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v')
  (e : u ⟶ v) (e' : u' ⟶ v') : e.cast hu hv = e' ↔ e = e'.cast hu.symm hv.symm :=
by { subst_vars, refl }

lemma hom.eq_cast_iff_cast_eq {u v u' v' : U} (hu : u = u') (hv : v = v')
  (e : u ⟶ v) (e' : u' ⟶ v') : e' = e.cast hu hv ↔ e'.cast hu.symm hv.symm = e :=
by { subst_vars, refl }

@[simp] lemma hom.cast_rfl_rfl {u v : U} (e : u ⟶ v) :
  e.cast rfl rfl = e := rfl

@[simp] lemma hom.cast_cast {u v u' v' u'' v'' : U} (e : u ⟶ v)
  (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
  (e.cast hu hv).cast hu' hv' = e.cast (hu.trans hu') (hv.trans hv') :=
by { subst_vars, refl }

lemma hom.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
  e.cast hu hv == e :=
by { subst_vars, refl }

lemma hom.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v')
  (e : u ⟶ v) (e' : u' ⟶ v') : e.cast hu hv = e' ↔ e == e' :=
by { rw hom.cast_eq_cast, exact cast_eq_iff_heq }

lemma hom.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v')
  (e : u ⟶ v) (e' : u' ⟶ v') : e' = e.cast hu hv ↔ e' == e :=
by { rw [eq_comm, hom.cast_eq_iff_heq], exact ⟨heq.symm, heq.symm⟩ }

/-- `cast`ing arrows along equality of endpoints defines an equivalence. -/
@[simps] def hom.equiv_cast {u u' v v' : U} (hu : u = u') (hv : v = v') :
  (u ⟶ v) ≃ (u' ⟶ v') :=
{ to_fun := λ e, e.cast hu hv,
  inv_fun := λ e, e.cast hu.symm hv.symm,
  left_inv := λ e, by simp,
  right_inv := λ e, by simp }

lemma _root_.prefunctor.map_cast_eq_of_eq {φ ψ : U ⥤q V} (h : φ = ψ) {u u' : U} (e : u ⟶ u') :
  (φ.map e).cast (congr_arg (λ (θ : U ⥤q V), θ.obj u) h : φ.obj u = ψ.obj u)
                 (congr_arg (λ θ : U ⥤q V, θ.obj u') h : φ.obj u' = ψ.obj u') = ψ.map e :=
by { cases h, refl, }

lemma _root_.prefunctor.map_cast (φ : U ⥤q V) {u₁ u₂ v₁ v₂ : U} (hu : u₁ = u₂) (hv : v₁ = v₂)
  (e : u₁ ⟶ v₁) :
  φ.map (hom.cast hu hv e) = (hom.cast (congr_arg φ.obj hu) (congr_arg φ.obj hv) (φ.map e)) :=
by { cases hu, cases hv, refl }

/-!
### Rewriting paths along equalities of vertices
-/

open path

/-- Change the endpoints of a path using equalities. -/
def path.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : path u v) : path u' v' :=
eq.rec (eq.rec p hv) hu

lemma path.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (p : path u v) :
  p.cast hu hv = cast (by rw [hu, hv]) p:=
eq.drec (eq.drec (eq.refl (path.cast (eq.refl u) (eq.refl v) p)) hu) hv

lemma path.cast_congr {u v u' v' : U} (hu hu' : u = u') (hv hv' : v = v') (e : path u v) :
  e.cast hu hv = e.cast hu' hv' :=
by { cases hu, cases hu', cases hv, cases hv', refl, }

@[simp] lemma path.cast_rfl_rfl {u v : U} (p : path u v) :
  p.cast rfl rfl = p := rfl

@[simp] lemma path.cast_cast {u v u' v' u'' v'' : U} (p : path u v)
  (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
  (p.cast hu hv).cast hu' hv' = p.cast (hu.trans hu') (hv.trans hv') :=
by { subst_vars, refl }

@[simp] lemma path.cast_nil {u u' : U} (hu : u = u') :
  (path.nil : path u u).cast hu hu = path.nil :=
by { subst_vars, refl }

lemma path.cast_heq {u v u' v' : U} (hu : u = u') (hv : v = v') (p : path u v) :
  p.cast hu hv == p :=
by { rw path.cast_eq_cast, exact cast_heq _ _ }

lemma path.cast_eq_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v')
  (p : path u v) (p' : path u' v') : p.cast hu hv = p' ↔ p == p' :=
by { rw path.cast_eq_cast, exact cast_eq_iff_heq }

lemma path.eq_cast_iff_heq {u v u' v' : U} (hu : u = u') (hv : v = v')
  (p : path u v) (p' : path u' v') : p' = p.cast hu hv ↔ p' == p :=
⟨λ h, ((p.cast_eq_iff_heq hu hv p').1 h.symm).symm,
 λ h, ((p.cast_eq_iff_heq hu hv p').2 h.symm).symm⟩

lemma path.cast_cons {u v w u' w' : U} (p : path u v) (e : v ⟶ w) (hu : u = u') (hw : w = w') :
  (p.cons e).cast hu hw = (p.cast hu rfl).cons (e.cast rfl hw) :=
by { subst_vars, refl }

lemma cast_eq_of_cons_eq_cons {u v v' w : U} {p : path u v} {p' : path u v'}
  {e : v ⟶ w} {e' : v' ⟶ w} (h : p.cons e = p'.cons e') :
  p.cast rfl (obj_eq_of_cons_eq_cons h) = p' :=
by { rw path.cast_eq_iff_heq, exact heq_of_cons_eq_cons h }

lemma hom_cast_eq_of_cons_eq_cons {u v v' w : U} {p : path u v} {p' : path u v'}
  {e : v ⟶ w} {e' : v' ⟶ w} (h : p.cons e = p'.cons e') :
  e.cast (obj_eq_of_cons_eq_cons h) rfl = e' :=
by { rw hom.cast_eq_iff_heq, exact hom_heq_of_cons_eq_cons h }

lemma cons_eq_cons_of_exist_cast {u v v' w : U} {p : path u v} {p' : path u v'}
  {e : v ⟶ w} {e' : v' ⟶ w} (hv : v = v') (he : e.cast hv rfl = e') (hp : p.cast rfl hv = p') :
  p.cons e = p'.cons e' :=
by { cases hv, cases he, cases hp, refl, }

lemma eq_nil_of_length_zero {u v : U} (p : path u v) (hzero : p.length = 0) :
  p.cast (eq_of_length_zero p hzero) rfl = path.nil :=
by { cases p; simpa only [nat.succ_ne_zero, length_cons] using hzero, }

end quiver
