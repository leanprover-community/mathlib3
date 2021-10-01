import topology.basic
import topology.opens
import topology.continuous_function.basic

open topological_space

variable (ι : Type)



namespace glue
structure glueing_datum :=
(space : ∀ (i : ι), Type)
(top : ∀ (i : ι), topological_space (space i))
(inter : ∀ (i j : ι), @opens (space i) (top i))
(trans : ∀ (i j : ι), @continuous_map (inter i j) (inter j i)
  (@subtype.topological_space (space i) (inter i j).1 (top i))
  (@subtype.topological_space (space j) (inter j i).1 (top j)))
(sinter : ∀ (i : ι), inter i i = ⊤)
(refl : ∀ (i : ι) (x : inter i i), trans i i x = x)
(tinter : ∀ (i j k : ι) (x : inter i j), (x.1 ∈ inter i k) → (trans i j x).1 ∈ inter j k)
(comm : ∀ (i j k : ι) (x : inter i j) (H : x.1 ∈ inter i k),
  (trans j k ⟨trans i j x, tinter i j k x H⟩).1 = (trans i k ⟨x, H⟩).1)

variables {ι} (𝔻 : glueing_datum ι)

attribute[simp] glueing_datum.sinter glueing_datum.refl glueing_datum.tinter glueing_datum.comm
attribute[instance] glueing_datum.top

namespace glueing_datum

def inter_top (i j : ι) : topological_space (𝔻.inter i j) := subtype.topological_space


@[simp] lemma inv (i j : ι) (x : 𝔻.inter i j) : 𝔻.trans j i (𝔻.trans i j x) = x := by {
  ext,
  convert 𝔻.comm i j i x (by { rw 𝔻.sinter i, simp }),
  { ext, refl },
  { simp },
}

def inter_homeo (i j : ι) : 𝔻.inter i j ≃ₜ 𝔻.inter j i := {
  to_fun := 𝔻.trans i j,
  inv_fun := 𝔻.trans j i,
  left_inv := λ x, 𝔻.inv i j x,
  right_inv := λ x, 𝔻.inv j i x,
}

lemma inv_if_in {i j: ι} (x : 𝔻.space i) (y : 𝔻.space j) (h₁ h₂)
  (H : (𝔻.trans i j ⟨x, h₁⟩).val = y) : x = (𝔻.trans j i ⟨y, h₂⟩).val := by simp[←H]

@[simp] lemma inv_iff (i j: ι) (x y) : 𝔻.trans j i x = y ↔ x = 𝔻.trans i j y :=
begin
  split,
  { intro H, simp[←H] },
  { intro H, simp[H] }
end

@[simp] lemma comm' (i j k : ι) (x : 𝔻.space i) (h₁ h₂) :
  (𝔻.trans j k ⟨(𝔻.trans i j ⟨x, h₁⟩).1, 𝔻.tinter i j k ⟨x, h₁⟩ h₂⟩).1 = (𝔻.trans i k ⟨x, h₂⟩).1 :=
by apply 𝔻.comm

def disjoint_set := Σ (i : ι), 𝔻.space i

def rel (x y : disjoint_set 𝔻) : Prop :=
∃ (H : x.2 ∈ 𝔻.inter x.1 y.1), (𝔻.trans x.1 y.1 ⟨x.2, H⟩).1 = y.2

lemma rel_refl : reflexive (rel 𝔻) := λ x, by split; simp

lemma rel_symm : symmetric (rel 𝔻) := λ x y h, by {
  obtain ⟨h₁, h₂⟩ := h,
  have hy: y.snd ∈ 𝔻.inter y.fst x.fst,
  { rw ← h₂, exact (𝔻.trans x.fst y.fst ⟨x.snd, h₁⟩).2 },
  split,
  suffices : ((𝔻.trans y.fst x.fst) ⟨y.snd, hy⟩) = ⟨x.2, h₁⟩,
  { convert (congr_arg subtype.val this) },
  simp[←h₂],
}

lemma rel_trans : transitive (rel 𝔻) := λ x y z h h', by {
  obtain ⟨h₁, h₂⟩ := rel_symm 𝔻 h,
  obtain ⟨h₃, h₄⟩ := h',
  obtain ⟨h₅, h₆⟩ := h,
  unfold rel at *,
  have := 𝔻.tinter _ _ _ ⟨y.2, h₁⟩ h₃,
  rw h₂ at this,
  use this,
  rw ← h₄,
  apply inv_if_in 𝔻,
  erw comm',
  exact h₆,
}

lemma rel_equiv : equivalence (rel 𝔻) := ⟨rel_refl 𝔻, rel_symm 𝔻, rel_trans 𝔻⟩

@[simp]
lemma rel_sinter {i : ι} (x y) : 𝔻.rel ⟨i, x⟩ ⟨i, y⟩ ↔ x = y := by {
  split,
  { intro H, obtain ⟨z, hz⟩ := H, simpa using hz, },
  { intro H, rw H, exact 𝔻.rel_refl _ }
}
def carrier := quot (rel 𝔻)

def immersion (i : ι) : 𝔻.space i → carrier 𝔻 := λ x, quot.mk (rel 𝔻) ⟨i, x⟩

@[simp] lemma immersion_eq_iff {i j : ι} {x y} :
  𝔻.immersion i x = 𝔻.immersion j y ↔ 𝔻.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  split,
  { intro H,
    erw [quot.eq, relation.eqv_gen_iff_of_equivalence (𝔻.rel_equiv)] at H,
    exact H },
  { intro H,
    exact quot.sound H }
end

instance carrier_topology : topological_space (carrier 𝔻) := {
  is_open := λ U, ∀ (i : ι), (𝔻.top i).is_open (set.preimage (immersion 𝔻 i) U),
  is_open_univ := λ i, (𝔻.top i).is_open_univ,
  is_open_inter := λ U V hU hV i, (𝔻.top i).is_open_inter _ _ (hU i) (hV i),
  is_open_sUnion := λ 𝒰 h i, by {
    simpa using (𝔻.top i).is_open_sUnion
      (set.image (set.preimage (immersion 𝔻 i)) 𝒰)
      (λ t ht, by {
        obtain ⟨U, hU₁, hU₂⟩ := ht,
        rw ← hU₂,
        exact h U hU₁ i,
      }),
  }
}

def inter_incl_l (i j : ι) : 𝔻.inter i j → 𝔻.space i := subtype.val
def inter_incl_r (i j : ι) : 𝔻.inter i j → 𝔻.space j := λ x, 𝔻.trans i j x

def inter_incl_l_continuous (i j : ι) : continuous (𝔻.inter_incl_l i j) := continuous_subtype_val
def inter_incl_r_continuous (i j : ι) : continuous (𝔻.inter_incl_r i j) :=
continuous.comp continuous_subtype_val (𝔻.trans i j).2

lemma image_preimage (i j : ι) (U) : 𝔻.immersion j ⁻¹' (𝔻.immersion i '' U)
  = (𝔻.inter_incl_r i j) '' (𝔻.inter_incl_l i j ⁻¹' U) :=
begin
  ext x,
  split,
  { intro H,
    obtain ⟨y, h₁, h₂⟩ := H,
    rw immersion_eq_iff at h₂,
    obtain ⟨z, h₃⟩ := h₂,
    use ⟨y, z⟩,
    exact ⟨h₁, h₃⟩ },
  { intro H,
    obtain ⟨y, h₁, h₂⟩ := H,
    use y.1,
    split,
    exact h₁,
    rw ← h₂,
    simp only [immersion_eq_iff],
    split,
    { simp[inter_incl_r] },
    { exact y.2 } }
end

def immersion_continuous (i : ι) : continuous (𝔻.immersion i) := ⟨λ _ hS, hS i⟩

def immersion_injective (i : ι) : function.injective (𝔻.immersion i) := λ _ _ h, by simpa using h

def immersion_open (i : ι) : is_open_map (𝔻.immersion i) := λ U hU, by {
  assume j : ι,
  have := (𝔻.trans i j).2.is_open_preimage, simp at this,
  rw image_preimage,
  erw set.image_comp coe (𝔻.trans i j),
  apply (𝔻.inter j i).2.open_embedding_subtype_coe.open_iff_image_open.mp,
  apply (homeomorph.is_open_image (𝔻.inter_homeo i j)).mpr,
  apply (𝔻.inter_incl_l_continuous i j).is_open_preimage _ hU,
}

def immersion_open_embedding (i : ι) : open_embedding (𝔻.immersion i) :=
open_embedding_of_continuous_injective_open
  (𝔻.immersion_continuous i) (𝔻.immersion_injective i) (𝔻.immersion_open i)




end glueing_datum


end glue
