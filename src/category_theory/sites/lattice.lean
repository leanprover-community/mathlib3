import Kenny.sites.basic order.complete_lattice

universes u v

namespace lattice

class Sup_lattice (X : Type u) extends lattice X, has_Sup X :=
(le_Sup : ∀ {s : set X} {a : X}, a ∈ s → a ≤ Sup s)
(Sup_le : ∀ {s : set X} {a : X}, (∀ (b : X), b ∈ s → b ≤ a) → Sup s ≤ a)

class Sup_distrib_lattice (X : Type u) extends Sup_lattice X :=
(inf_Sup_le {} : ∀ {x : X} {s : set X}, x ⊓ lattice.Sup s ≤ lattice.Sup ((⊓) x '' s))

section Sup_lattice

instance complete_lattice.to_Sup_lattice {X : Type u} [complete_lattice X] : Sup_lattice X :=
{ .. (infer_instance : complete_lattice X) }

variables {X : Type u} [Sup_lattice X]

theorem le_Sup' {s : set X} {a : X} : a ∈ s → a ≤ Sup s :=
Sup_lattice.le_Sup

theorem Sup_le' {s : set X} {a : X} : (∀ (b : X), b ∈ s → b ≤ a) → Sup s ≤ a :=
Sup_lattice.Sup_le

theorem Sup_singleton' (x : X) : Sup {x} = x :=
le_antisymm (Sup_le' $ λ b hb, set.eq_of_mem_singleton hb ▸ le_refl _) $
le_Sup' $ set.mem_singleton x

end Sup_lattice

section Sup_discrete_lattice

instance complete_distrib_lattice.to_Sup_distrib_lattice {X : Type u} [complete_distrib_lattice X] : Sup_distrib_lattice X :=
{ inf_Sup_le := λ x s, by rw [inf_Sup_eq, Sup_image],
  .. (infer_instance : complete_distrib_lattice X) }

variables {X : Type u} [Sup_distrib_lattice X]

theorem inf_Sup {x : X} {s : set X} : x ⊓ lattice.Sup s = lattice.Sup ((⊓) x '' s) :=
le_antisymm Sup_distrib_lattice.inf_Sup_le $ Sup_le' $ λ b ⟨c, hcs, hxcb⟩, hxcb ▸ inf_le_inf (le_refl x) (le_Sup' hcs)

end Sup_discrete_lattice

end lattice

namespace category_theory

open lattice

variables {X : Type u}

class is_univalent (X : Type u) [category.{v} X] : Prop :=
(univalent : ∀ x y : X, ∀ e : x ≅ y, x = y)

theorem eq_of_iso [category.{v} X] [is_univalent X] {x y : X} (e : x ≅ y) : x = y :=
is_univalent.univalent x y e

instance is_univalent_partial_order [partial_order X] : is_univalent X :=
⟨λ x y e, le_antisymm e.1.1.1 e.2.1.1⟩

instance semilattice_inf.has_pullback [semilattice_inf X] : has_pullback X :=
λ F,
{ cone :=
  { X := F.obj pullback_diagram.base_left ⊓ F.obj pullback_diagram.base_right,
    π :=
    { app := λ p, pullback_diagram.rec_on p ⟨⟨inf_le_left⟩⟩ ⟨⟨inf_le_right⟩⟩
        ⟨⟨le_trans inf_le_left (F.map pullback_diagram.hom.to_target_left).down.down⟩⟩,
      naturality' := by intros; ext } },
  is_limit :=
  { lift := λ c, ⟨⟨le_inf (c.π.app pullback_diagram.base_left).down.down (c.π.app pullback_diagram.base_right).down.down⟩⟩,
    fac' := by intros; ext,
    uniq' := by intros; ext } }

instance Sup_lattice.has_site [Sup_distrib_lattice X] : has_site X :=
{ cov := λ U, { c | U ≤ Sup (sigma.fst '' c) },
  iso_mem := λ U V e, show U ≤ _, by rw [set.image_singleton, Sup_singleton']; exact e.2.1.1,
  comp_mem := λ U S HS F HF, le_trans HS $ Sup_le' $ λ x hx, let ⟨m, hmS, hmx⟩ := hx in
    hmx ▸ le_trans (HF m hmS) (Sup_le' $ λ y hy, let ⟨n, hnFS, hny⟩ := hy in
      le_Sup' ⟨⟨n.1, ⟨⟨le_trans n.2.1.1 m.2.1.1⟩⟩⟩, ⟨m, hmS, n, hnFS, rfl⟩, hny⟩),
  pullback_mem := λ U S HS V f,
  calc  V
      ≤ V ⊓ Sup (sigma.fst '' S) : le_inf (le_refl V) (le_trans f.1.1 HS)
  ... = Sup ((⊓) V '' (sigma.fst '' S)) : inf_Sup
  ... = Sup ((⊓) V ∘ sigma.fst '' S) : congr_arg Sup (set.image_comp _ _ S).symm
  ... ≤ Sup (sigma.fst '' {m | ∃ t ∈ S, (⟨_, pullback.fst f t.2⟩ : Σ W, W ⟶ V) = m}) :
    Sup_le' (λ b ⟨c, hcs, hb⟩, le_Sup' ⟨⟨V ⊓ c.1, ⟨⟨inf_le_left⟩⟩⟩, ⟨c, hcs, rfl⟩, hb⟩) }

end category_theory
