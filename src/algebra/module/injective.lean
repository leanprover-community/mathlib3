/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import algebra.category.Module.basic
import ring_theory.ideal.basic

/-!
# Injective modules

## Main definitions

* `module.injective`: an `R`-module `Q` is injective if and only if for every injective `R`-linear
  map descents to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `ideal R`
  extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `module.Baer.criterion`: an `R`-module is injective if it is Baer.

-/


noncomputable theory

universes u v

variables (R : Type u) [ring R] (Q : Type (max u v)) [add_comm_group Q] [module R Q]

class module.injective : Prop :=
(out : ∀ (X Y : Type (max u v)) [add_comm_group X] [add_comm_group Y] [module R X] [module R Y]
  (f : X →ₗ[R] Y) (hf : function.injective f) (g : X →ₗ[R] Q),
  ∃ (h : Y →ₗ[R] Q), ∀ x, h (f x) = g x)

def module.Baer : Prop := ∀ (I : ideal R) (g : I →ₗ[R] Q), ∃ (g' : R →ₗ[R] Q),
  ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩

namespace Baer

open zorn

variables {R} {M N : Type (max u v)} [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N] {i : M →ₗ[R] N} (hi : function.injective i) (f : M →ₗ[R] Q)
variable {Q}
include hi

structure submodule_between extends submodule R N :=
(le : i.range ≤ to_submodule)
(extension : to_submodule →ₗ[R] Q)
(is_extension: ∀ (m : M), f m = extension ⟨i m, le ⟨m, rfl⟩⟩)

@[ext]
lemma ext (a b : submodule_between hi f) (submodule_eq : a.to_submodule = b.to_submodule)
  (extension_eq : ∀ x, a.extension x = b.extension ⟨x.1, submodule_eq ▸ x.2⟩) :
  a = b :=
begin
  rcases a with ⟨a, a_le, e1, _⟩,
  rcases b with ⟨b, b_le, e2, _⟩,
  dsimp at *,
  subst submodule_eq,
  have le_eq : a_le = b_le := rfl,
  subst le_eq,
  have ext_eq : e1 = e2,
  { ext z,
    convert extension_eq z,
    rw subtype.ext_iff_val,
    refl, },
  subst ext_eq,
end

lemma ext_iff (a b : submodule_between hi f) :
  a = b ↔ ∃ (submodule_eq : a.to_submodule = b.to_submodule),
    ∀ x, a.extension x = b.extension ⟨x.1, submodule_eq ▸ x.2⟩ :=
⟨λ r, begin
  induction r,
  refine ⟨rfl, λ x, _⟩,
  congr,
  rw subtype.ext_iff_val,
end, λ ⟨h1, h2⟩, Baer.ext _ _ a b h1 h2⟩

instance : has_bot (submodule_between hi f) :=
{ bot :=
  { to_submodule := i.range,
    le := le_refl _,
    extension :=
      { to_fun := λ x, f x.2.some,
        map_add' := λ x y, begin
          have eq1 : i x.2.some = x.1 := x.2.some_spec,
          have eq2 : i y.2.some = y.1 := y.2.some_spec,
          have eq3 : i (x + y).2.some = x.1 + y.1 := (x + y).2.some_spec,
          have eq4 := congr_arg2 (+) eq1 eq2,
          rw [← map_add, ← eq3] at eq4,
          clear eq1 eq2 eq3,
          replace eq4 := hi eq4,
          rw [← eq4, map_add],
        end,
        map_smul' := λ r x, begin
          rw ring_hom.id_apply,
          have eq1 : i x.2.some = x.1 := x.2.some_spec,
          have eq2 : i (r • x).2.some = r • x.1 := (r • x).2.some_spec,
          have eq3 := congr_arg ((•) r) eq1,
          rw [← linear_map.map_smul, ← eq2] at eq3,
          replace eq3 := hi eq3,
          clear eq1 eq2,
          rw [← eq3, linear_map.map_smul],
        end },
    is_extension := λ m, begin
      simp only [linear_map.coe_mk],
      have eq1 : i (⟨i m, ⟨_, rfl⟩⟩ : i.range).2.some = i m :=
        (⟨i m, ⟨_, rfl⟩⟩ : i.range).2.some_spec,
      replace eq1 := hi eq1,
      erw eq1,
    end } }

instance : inhabited (submodule_between hi f) := ⟨⊥⟩

instance : has_le (submodule_between hi f) :=
{ le := λ X1 X2,
    nonempty
      Σ' (h : X1.to_submodule ≤ X2.to_submodule),
        ∀ (m : X1.to_submodule), X2.extension ⟨m, h m.2⟩ = X1.extension m }

instance : partial_order (submodule_between hi f) :=
{ le := (≤),
  le_refl := λ a, nonempty.intro
    ⟨le_refl _, λ _, by congr'; rw subtype.ext_iff_val; refl ⟩,
  le_antisymm := λ a b ⟨⟨le_ab, hab⟩⟩ ⟨⟨le_ba, hba⟩⟩,
    let m_eq : a.to_submodule = b.to_submodule := (le_antisymm le_ab le_ba) in
    ext _ _ _ _ m_eq (λ x, by { convert hba ⟨x, m_eq ▸ x.2⟩, rw subtype.ext_iff_val, refl }),
  le_trans := λ a b c ⟨⟨le_ab, hab⟩⟩ ⟨⟨le_bc, hbc⟩⟩, nonempty.intro
    ⟨le_trans le_ab le_bc, λ z, by rw [← hab z, ← hbc ⟨z, le_ab z.2⟩]; refl⟩ }

variables {R i hi f}
lemma directed_on' {c : set (submodule_between hi f)} (hchain : chain (≤) c) :
  directed_on (≤) c :=
begin
  rw directed_on_iff_directed,
  convert directed_of_chain hchain,
end

lemma exists3 {c : set (submodule_between hi f)} (hchain : chain (≤) c) {α β γ}
  (mem1 : α ∈ c) (mem2 : β ∈ c) (mem3 : γ ∈ c) :
  ∃ (z) (mem4 : z ∈ c), α ≤ z ∧ β ≤ z ∧ γ ≤ z :=
begin
  rcases directed_on' hchain _ mem1 _ mem2 with ⟨z1, ⟨z1_mem, hz1⟩⟩,
  rcases directed_on' hchain z1 z1_mem _ mem3 with ⟨z, ⟨z_mem, hz⟩⟩,
  exact ⟨z, z_mem, le_trans hz1.1 hz.1, le_trans hz1.2 hz.1, hz.2⟩,
end

lemma chain_submodule_of_chain_submodule_between
  {c : set (submodule_between hi f)} (hchain : chain (≤) c) :
  (chain (≤) $ (λ x : submodule_between hi f, x.to_submodule) '' c) :=
begin
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ (neq : a.to_submodule ≠ b.to_submodule),
  specialize hchain a_mem b_mem
    (λ r, neq $ r ▸ rfl),
  rcases hchain,
  work_on_goal 1 { left },
  work_on_goal 2 { right },
  all_goals { rcases hchain with ⟨⟨le1, -⟩⟩, exact le1 },
end

lemma submodule_le_of_submodule_between_le {a b : submodule_between hi f} (le1 : a ≤ b) :
  a.to_submodule ≤ b.to_submodule := le1.some.1

lemma directed_on_of_chain {c : set (submodule_between hi f)} (hchain : chain (≤) c) :
  directed_on (≤) $ (λ x : submodule_between hi f, x.to_submodule) '' c :=
begin
  rw directed_on_iff_directed,
  rintros ⟨_, ⟨a, a_mem, rfl⟩⟩ ⟨_, ⟨b, b_mem, rfl⟩⟩,
  by_cases eq1 : a = b,
  { refine ⟨⟨a.to_submodule, ⟨_, a_mem, rfl⟩⟩, le_refl _, _⟩,
    simp only [eq1],
    exact le_refl _, },
  { refine or.elim (hchain a_mem b_mem eq1)
      (λ h, ⟨⟨b.to_submodule, ⟨_, b_mem, rfl⟩⟩, submodule_le_of_submodule_between_le h, le_refl _⟩)
      (λ h, ⟨⟨a.to_submodule, ⟨_, a_mem, rfl⟩⟩, le_refl _, submodule_le_of_submodule_between_le h⟩)}
end

lemma nonempty_of_submodule_between {c : set (submodule_between hi f)} (hnonempty : c.nonempty) :
  ((λ x : submodule_between hi f, x.to_submodule) '' c).nonempty :=
⟨hnonempty.some.to_submodule, ⟨_, hnonempty.some_spec, rfl⟩⟩

def pick_submodule {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  submodule R N :=
((submodule.mem_Sup_of_directed (nonempty_of_submodule_between hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some

lemma pick_submodule_mem_image {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  pick_submodule hchain hnonempty y ∈ ((λ x : submodule_between hi f, x.to_submodule) '' c) :=
((submodule.mem_Sup_of_directed (nonempty_of_submodule_between hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some

def pick_submodule_between {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  submodule_between hi f :=
((submodule.mem_Sup_of_directed (nonempty_of_submodule_between hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some.some

lemma pick_submodule_between_mem {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  pick_submodule_between hchain hnonempty y ∈ c :=
((submodule.mem_Sup_of_directed (nonempty_of_submodule_between hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some.some_spec.1

lemma pick_submodule_between_to_submodule_mem
  {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  y.1 ∈ (pick_submodule_between hchain hnonempty y).to_submodule :=
begin
  unfold pick_submodule_between,
  generalize_proofs h mem1,
  generalize_proofs at mem1,
  generalize_proofs,
  have eq1 : mem1.some.to_submodule = _ := mem1.some_spec.2,
  rw eq1,
  convert h.some_spec.some_spec,
end

lemma pick_submodule_mem {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c)) :
  y.1 ∈ pick_submodule hchain hnonempty y :=
((submodule.mem_Sup_of_directed (nonempty_of_submodule_between hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some_spec

def submodule_between.max_extension {c : set (submodule_between hi f)}
  (hchain : chain (≤) c) (hnonempty : c.nonempty) :
  Sup ((λ x : submodule_between hi f, x.to_submodule) '' c) → Q :=
λ y, (pick_submodule_between hchain hnonempty y).extension
  ⟨y.1, by apply pick_submodule_between_to_submodule_mem⟩

lemma submodule_between.max_extension_property {c : set (submodule_between hi f)}
  (hchain : chain (≤) c) (hnonempty : c.nonempty)
  (x : Sup ((λ x : submodule_between hi f, x.to_submodule) '' c))
  {γ : submodule_between hi f} (mem1 : γ ∈ c)
  (mem2 : x.1 ∈ γ.to_submodule) :
  submodule_between.max_extension hchain hnonempty x = γ.extension ⟨x.1, mem2⟩ :=
begin
  unfold submodule_between.max_extension,
  generalize_proofs mem3,
  by_cases eq_ineq : pick_submodule_between hchain hnonempty x = γ,
  { rw ext_iff at eq_ineq,
    rcases eq_ineq with ⟨h1, h2⟩,
    convert h2 _, },
  { rcases hchain (pick_submodule_between_mem hchain hnonempty x) mem1 eq_ineq with
      ⟨⟨le1, h1⟩⟩|⟨⟨le1, h1⟩⟩,
    all_goals {
      rw ← h1 ⟨x.1, by assumption⟩,
      congr, } },
end

lemma submodule_between.max_extension.map_add {c : set (submodule_between hi f)}
  (hchain : chain (≤) c) (hnonempty : c.nonempty) (y1 y2):
  submodule_between.max_extension hchain hnonempty (y1 + y2) =
  submodule_between.max_extension hchain hnonempty y1 +
  submodule_between.max_extension hchain hnonempty y2 :=
begin
  have mem_y1 := pick_submodule_between_to_submodule_mem hchain hnonempty y1,
  have mem_y2 := pick_submodule_between_to_submodule_mem hchain hnonempty y2,
  have mem_add :=  pick_submodule_between_to_submodule_mem hchain hnonempty (y1 + y2),
  rw submodule_between.max_extension_property hchain hnonempty y1
    (pick_submodule_mem_image hchain hnonempty y1).some_spec.1 mem_y1,
  rw submodule_between.max_extension_property hchain hnonempty y2
    (pick_submodule_mem_image hchain hnonempty y2).some_spec.1 mem_y2,
  rw submodule_between.max_extension_property hchain hnonempty _
    (pick_submodule_mem_image hchain hnonempty _).some_spec.1 mem_add,
  generalize_proofs hadd hy1 hy2,
  have := exists3 hchain hadd.some_spec.1 hy1.some_spec.1 hy2.some_spec.1,
  rcases this with ⟨z, z_mem, ⟨⟨z_le1, h1⟩⟩, ⟨⟨z_le2, h2⟩⟩, ⟨⟨z_le3, h3⟩⟩⟩,
  rw [← h1, ← h2, ← h3, ← map_add],
  congr,
end

lemma submodule_between.max_extension.map_smul {c : set (submodule_between hi f)}
  (hchain : chain (≤) c) (hnonempty : c.nonempty) (r : R) (y):
  submodule_between.max_extension hchain hnonempty (r • y) =
  r • submodule_between.max_extension hchain hnonempty y :=
begin
  have mem_y := pick_submodule_between_to_submodule_mem hchain hnonempty y,
  have mem_smul := pick_submodule_between_to_submodule_mem hchain hnonempty (r • y),
  rw submodule_between.max_extension_property hchain hnonempty y
    (pick_submodule_mem_image hchain hnonempty y).some_spec.1 mem_y,
  rw submodule_between.max_extension_property hchain hnonempty (r • y)
    (pick_submodule_mem_image hchain hnonempty (r • y)).some_spec.1 mem_smul,
  generalize_proofs inst hsmul hy,
  resetI,
  rcases directed_on' hchain _ hsmul.some_spec.1 _ hy.some_spec.1 with
    ⟨z, z_mem, ⟨⟨z_le1, h1⟩⟩, ⟨⟨z_le2, h2⟩⟩⟩,
  rw [← h1, ← linear_map.map_smul, ← h2],
  congr,
end

def submodule_between.max {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) :
  submodule_between hi f :=
{ to_submodule := Sup ((λ x : submodule_between hi f, x.to_submodule) '' c),
  le := begin
    cases hnonempty with j hj,
    exact le_trans j.le (le_Sup ⟨j, hj, rfl⟩),
  end,
  extension :=
  { to_fun := submodule_between.max_extension hchain hnonempty,
    map_add' := submodule_between.max_extension.map_add hchain hnonempty,
    map_smul' := submodule_between.max_extension.map_smul hchain hnonempty },
  is_extension := λ m, begin
    dsimp,
    generalize_proofs im_mem,
    change _ = (pick_submodule_mem_image hchain hnonempty ⟨i m, im_mem⟩).some.extension _,
    generalize_proofs mem_image mem_submodule,
    generalize_proofs at mem_submodule,
    rw (Exists.some mem_image).is_extension m,
    congr,
  end }

lemma submodule_between.le_max {c : set (submodule_between hi f)} (hchain : chain (≤) c)
  (hnonempty : c.nonempty) (a : submodule_between hi f) (ha : a ∈ c) :
  a ≤ submodule_between.max hchain hnonempty :=
begin
  unfold submodule_between.max,
  refine ⟨⟨le_Sup ⟨a, ha, rfl⟩, _⟩⟩,
  dsimp,
  unfold submodule_between.max_extension,
  generalize_proofs mem1 mem_image mem2,
  dsimp only at *,
  by_cases eq_ineq : pick_submodule_between hchain hnonempty ⟨↑m, mem1⟩ = a,
  { rw ext_iff at eq_ineq,
    rcases eq_ineq with ⟨h1, h2⟩,
    convert h2 _,
    rw subtype.ext_iff_val,
    refl, },
  { rcases hchain (pick_submodule_between_mem hchain hnonempty _) ha eq_ineq with
      ⟨⟨le1, h1⟩⟩|⟨le1, h1⟩,
    symmetry,
    all_goals { convert h1 _; rw subtype.ext_iff_val; refl }, },
end

lemma submodule_between.aux1 : ∀ (c : set (submodule_between hi f)),
  chain has_le.le c →
  c.nonempty →
  (∃ (ub : submodule_between hi f), ∀ (a : submodule_between hi f), a ∈ c → a ≤ ub) :=
λ c hchain hnonempty,
  ⟨submodule_between.max hchain hnonempty, submodule_between.le_max hchain hnonempty⟩

variables (hi f)
def submodule_between_max : submodule_between hi f :=
  (@zorn_nonempty_partial_order (submodule_between hi f) _ _ (submodule_between.aux1)).some

def submodule_between_max_is_max :=
  (@zorn_nonempty_partial_order (submodule_between hi f) _ _ (submodule_between.aux1)).some_spec

variables {hi f}
def submodule_between_max_adjoin.aux1
  {y : N}
  (x : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}) :
  ∃ (a : (submodule_between_max hi f).to_submodule) (b : R), x.1 = a.1 + b • y :=
begin
  have mem1 : x.1 ∈ (_ : set _) := x.2,
  rw submodule.coe_sup at mem1,
  rcases mem1 with ⟨a, b, a_mem, (b_mem : b ∈ (submodule.span R _ : submodule R N)), eq1⟩,
  rw submodule.mem_span_singleton at b_mem,
  rcases b_mem with ⟨z, eq2⟩,
  refine ⟨⟨a, a_mem⟩, z, _⟩,
  rw [← eq1, eq2],
end

def submodule_between_max_adjoin.fst
  {y : N}
  (x : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}) :
  (submodule_between_max hi f).to_submodule :=
(submodule_between_max_adjoin.aux1 x).some

def submodule_between_max_adjoin.snd
  {y : N}
  (x : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}) :
  R :=
(submodule_between_max_adjoin.aux1 x).some_spec.some

lemma submodule_between_max_adjoin.eqn
  {y : N}
  (x : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}) :
  x.1 = (submodule_between_max_adjoin.fst x).1 + (submodule_between_max_adjoin.snd x) • y :=
(submodule_between_max_adjoin.aux1 x).some_spec.some_spec

variables (hi f)
def submodule_between_max_adjoin.ideal (y : N) :
  ideal R :=
{ carrier := {r | r • y ∈ (submodule_between_max hi f).to_submodule},
  add_mem' := λ a b (ha : a • y ∈ _) (hb : b • y ∈ _), begin
    change (a + b) • _ ∈ _,
    rw [add_smul],
    exact submodule.add_mem _ ha hb,
  end,
  smul_mem' := λ c x (hx : x • y ∈ _), begin
    change (_ • _) • _ ∈ _,
    rw [smul_eq_mul, mul_smul],
    exact submodule.smul_mem _ _ hx,
  end,
  zero_mem' := by simp }

def submodule_between_max_adjoin.ideal_to (y : N) :
  submodule_between_max_adjoin.ideal hi f y →ₗ[R] Q :=
{ to_fun := λ z, (submodule_between_max hi f).extension ⟨z.1 • y, z.2⟩,
  map_add' := λ z1 z2, by rw [← map_add]; congr; erw add_smul,
  map_smul' := λ z1 z2, begin
    rw [ring_hom.id_apply, ← linear_map.map_smul],
    congr' 1,
    rw subtype.ext_iff_val,
    dsimp,
    rw mul_smul,
  end }

def submodule_between_max_adjoin.aux2 (h : module.Baer R Q) (y : N) :=
  h (submodule_between_max_adjoin.ideal hi f y) (submodule_between_max_adjoin.ideal_to hi f y)

def submodule_between_max_adjoin.extend_ideal_to (h : module.Baer R Q) (y : N) :
  R →ₗ[R] Q :=
(submodule_between_max_adjoin.aux2 hi f h y).some

lemma submodule_between_max_adjoin.extend_ideal_to_is_extension (h : module.Baer R Q) (y : N) :
  ∀ (x : R) (mem : x ∈ submodule_between_max_adjoin.ideal hi f y),
  submodule_between_max_adjoin.extend_ideal_to hi f h y x =
  submodule_between_max_adjoin.ideal_to hi f y ⟨x, mem⟩ :=
(submodule_between_max_adjoin.aux2 hi f h y).some_spec

lemma submodule_between_max_adjoin.extend_ideal_to_wd' (h : module.Baer R Q) {y : N} (r : R)
  (eq1 : r • y = 0) :
  submodule_between_max_adjoin.extend_ideal_to hi f h y r = 0 :=
begin
  rw submodule_between_max_adjoin.extend_ideal_to_is_extension hi f h y r begin
    change r • y ∈ _,
    rw eq1,
    exact submodule.zero_mem _,
  end,
  unfold submodule_between_max_adjoin.ideal_to,
  simp only [linear_map.coe_mk, eq1],
  convert map_zero _,
end

lemma submodule_between_max_adjoin.extend_ideal_to_wd (h : module.Baer R Q) {y : N} (r r' : R)
  (eq1 : r • y = r' • y) :
  submodule_between_max_adjoin.extend_ideal_to hi f h y r =
  submodule_between_max_adjoin.extend_ideal_to hi f h y r' :=
begin
  rw [← sub_eq_zero, ← map_sub],
  convert submodule_between_max_adjoin.extend_ideal_to_wd' hi f h (r - r') _,
  rw [sub_smul, sub_eq_zero, eq1],
end

lemma submodule_between_max_adjoin.extend_ideal_to_eq (h : module.Baer R Q) {y : N} (r : R)
  (hr : r • y ∈ (submodule_between_max hi f).to_submodule) :
  submodule_between_max_adjoin.extend_ideal_to hi f h y r =
  (submodule_between_max hi f).extension ⟨r • y, hr⟩ :=
begin
  rw submodule_between_max_adjoin.extend_ideal_to_is_extension hi f h _ _ hr,
  refl,
end

def submodule_between_max_adjoin.extension_to_fun (h : module.Baer R Q)
  {y : N} :
  (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y} →  Q :=
λ x, (submodule_between_max hi f).extension (submodule_between_max_adjoin.fst x) +
  submodule_between_max_adjoin.extend_ideal_to hi f h y (submodule_between_max_adjoin.snd x)

lemma submodule_between_max_adjoin.extension_to_fun_wd (h : module.Baer R Q)
  {y : N} (x : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y})
  (a : (submodule_between_max hi f).to_submodule) (r : R)
  (eq1 : x.1 = a.1 + r • y) :
  submodule_between_max_adjoin.extension_to_fun hi f h x =
  (submodule_between_max hi f).extension a +
  submodule_between_max_adjoin.extend_ideal_to hi f h y r :=
begin
  have eq2 := eq1,
  rw [submodule_between_max_adjoin.eqn, ← sub_eq_zero,
    show ∀ (a b c d : N), (a + b) - (c + d) = (a - c) - (d - b), from λ _ _ _ _, by abel,
    sub_eq_zero, ← sub_smul] at eq2,
  have eq3 := submodule_between_max_adjoin.extend_ideal_to_eq hi f h
    (r - submodule_between_max_adjoin.snd x) begin
      rw ← eq2,
      exact submodule.sub_mem _ (submodule_between_max_adjoin.fst x).2 a.2,
    end,
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3,
  unfold submodule_between_max_adjoin.extension_to_fun,
  rw [eq3, ← add_assoc],
  congr' 1,
  rw [← map_add, show ∀ (a b : (submodule_between_max hi f).to_submodule), a + b = ⟨a.1 + b.1, _⟩,
    from λ _ _, rfl],
  have eq4 := submodule_between_max_adjoin.eqn x,
  rw eq1 at eq4,
  simp only [eq4, add_sub, add_sub_cancel],
  congr' 1,
  rw subtype.ext_iff_val,
end

def submodule_between_max_adjoin (h : module.Baer R Q) {y : N}
  (hy : y ∉ (submodule_between_max hi f).to_submodule) :
  submodule_between hi f :=
{ to_submodule := (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y},
  le := le_trans (submodule_between_max hi f).le le_sup_left,
  extension :=
    { to_fun := submodule_between_max_adjoin.extension_to_fun hi f h,
      map_add' := λ a b, begin
        have eq1 : (a + b).val =
          ((submodule_between_max_adjoin.fst a) + (submodule_between_max_adjoin.fst b)).1 +
          (submodule_between_max_adjoin.snd a + submodule_between_max_adjoin.snd b) • y,
        { change a.1 + b.1 = _ + _,
          rw [submodule_between_max_adjoin.eqn, submodule_between_max_adjoin.eqn, add_smul],
          change _ = _ + _ + _,
          abel, },
        rw [submodule_between_max_adjoin.extension_to_fun_wd hi f h (a + b) _ _ eq1, map_add,
          map_add],
        unfold submodule_between_max_adjoin.extension_to_fun,
        abel,
      end,
      map_smul' := λ r a, begin
        rw [ring_hom.id_apply],
        have eq1 : (r • a).1 = (r • submodule_between_max_adjoin.fst a).1 +
          (r • submodule_between_max_adjoin.snd a) • y,
        { change r • a.1 = _,
          rw [submodule_between_max_adjoin.eqn, smul_add, smul_eq_mul, mul_smul],
          refl, },
        rw [submodule_between_max_adjoin.extension_to_fun_wd hi f h (r • a) _ _ eq1,
          linear_map.map_smul, linear_map.map_smul, ← smul_add],
        congr',
      end },
  is_extension := λ m, begin
    simp only [linear_map.coe_mk],
    generalize_proofs mem,
    rw (submodule_between_max hi f).is_extension,
    have eq1 : (⟨i m, mem⟩ : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}).1 =
      (⟨i m, (submodule_between_max hi f).le ⟨_, rfl⟩⟩ :
        (submodule_between_max hi f).to_submodule).1 + (0 : R) • y,
    { rw [zero_smul, add_zero], },
    rw [submodule_between_max_adjoin.extension_to_fun_wd hi f h ⟨i m, mem⟩
      ⟨i m, (submodule_between_max hi f).le ⟨_, rfl⟩⟩ 0 eq1, map_zero, add_zero],
  end }

lemma submodule_between_max_le (h : module.Baer R Q) {y : N}
  (hy : y ∉ (submodule_between_max hi f).to_submodule) :
  submodule_between_max hi f ≤ submodule_between_max_adjoin hi f h hy := nonempty.intro
⟨le_sup_left, λ m, begin
  generalize_proofs mem,
  have eq1 : (⟨m, mem⟩ : (submodule_between_max hi f).to_submodule ⊔ submodule.span R {y}).1 =
      m.1 + (0 : R) • y,
    { rw [zero_smul, add_zero], refl, },
  change submodule_between_max_adjoin.extension_to_fun hi f h _ = _,
  rw [submodule_between_max_adjoin.extension_to_fun_wd hi f h _ _ _ eq1, map_zero, add_zero],
end⟩

lemma submodule_between_max_eq (h : module.Baer R Q) {y : N}
  (hy : y ∉ (submodule_between_max hi f).to_submodule) :
  submodule_between_max_adjoin hi f h hy = submodule_between_max hi f :=
submodule_between_max_is_max hi f _ (submodule_between_max_le hi f h hy)

lemma submodule_between_max_to_submodule_eq_top (h : module.Baer R Q) :
  (submodule_between_max hi f).to_submodule = ⊤ :=
begin
  by_contra rid,
  rcases show ∃ (y : N), y ∉ (submodule_between_max hi f).to_submodule,
  { contrapose! rid,
    ext,
    exact ⟨λ _, trivial, λ _, rid _⟩, } with ⟨y, hy⟩,
  have : (submodule_between_max_adjoin hi f h hy).to_submodule = _ :=
  by rw submodule_between_max_eq hi f h hy,
  change _ ⊔ _ = _ at this,
  apply hy,
  rw ← this,
  rw submodule.mem_sup,
  exact ⟨0, submodule.zero_mem _, y, submodule.mem_span_singleton_self _, zero_add _⟩,
end

theorem criterion (h : module.Baer R Q) :
  module.injective R Q :=
{ out := λ X Y ins1 ins2 ins3 ins4 i hi f, begin
  resetI,
  have eq1 := submodule_between_max_to_submodule_eq_top hi f h,
  set f'' : (⊤ : submodule R Y) →ₗ[R] Q :=
  { to_fun := λ y, (submodule_between_max hi f).extension ⟨y.1, by { rw eq1, exact y.2}⟩,
    map_add' := λ x y, by { dsimp, rw ← map_add,  congr' 1 },
    map_smul' := λ r x, by { dsimp, rw ← linear_map.map_smul, congr' 1 } } with f''_eq,
  refine ⟨{ to_fun := λ y, f'' ⟨y, trivial⟩, map_add' := λ x y, begin
    rw ← map_add,
    congr',
  end, map_smul' := λ r x, begin
    rw [ring_hom.id_apply, ← linear_map.map_smul],
    refl,
  end }, _⟩,
  intros x,
  have is_extension := (submodule_between_max hi f).is_extension x,
  simp only [linear_map.coe_mk],
  rw is_extension,
end }

end Baer
