import set_theory.cardinal
import set_theory.ordinal_arithmetic
import data.W

universes u v w

variables {α : Type u} {β : α → Type u}

noncomputable theory

open cardinal

set_option pp.universes true

namespace W_type

def to_sigma : W_type β → Σ a : α, β a → W_type β
| ⟨a, f⟩ := ⟨a, f⟩

def of_sigma : (Σ a : α, β a → W_type β) → W_type β
| ⟨a, f⟩ := W_type.mk a f

@[simp] lemma of_sigma_to_sigma : Π (w : W_type β),
  of_sigma (to_sigma w) = w
| ⟨a, f⟩ := rfl

@[simp] lemma to_sigma_of_sigma : Π (s : Σ a : α, β a → W_type β),
  to_sigma (of_sigma s) = s
| ⟨a, f⟩ := rfl

def equiv_sigma : W_type β ≃ Σ a : α, β a → W_type β :=
{ to_fun := to_sigma,
  inv_fun := of_sigma,
  left_inv := of_sigma_to_sigma,
  right_inv := to_sigma_of_sigma }

def to_type (γ : Type w) (fγ : Π a : α, (β a → γ) → γ) : W_type β → γ
| ⟨a, f⟩ := fγ a (λ b, to_type (f b))

lemma to_type_injective (γ : Type w) (fγ : Π a : α, (β a → γ) → γ)
  (fγ_injective : ∀ a₁ a₂ f₁ f₂, fγ a₁ f₁ = fγ a₂ f₂ →
    (⟨a₁, f₁⟩ : Σ a : α, (β a → γ)) = ⟨a₂, f₂⟩) :
  function.injective (to_type γ fγ)
| ⟨a₁, f₁⟩ ⟨a₂, f₂⟩ := begin
  rw [to_type, to_type],
  intro h,
  rcases sigma.mk.inj (fγ_injective _ _ _ _ h) with ⟨rfl, h⟩,
  simp only [function.funext_iff, heq_iff_eq] at h,
  congr,
  ext,
  exact to_type_injective (h x)
end

lemma cardinal_mk_eq_sum : cardinal.mk  (W_type β) =
  cardinal.sum (λ a : α, cardinal.mk (W_type β) ^ cardinal.mk.{u} (β a)) :=
begin
  simp only [cardinal.power_def, cardinal.sum_mk],
  exact le_antisymm ⟨equiv_sigma.to_embedding⟩ ⟨equiv_sigma.symm.to_embedding⟩
end
#print cardinal.min
lemma cardinal_mk_eq_min : cardinal.mk (W_type β) =
  @cardinal.min { c : cardinal.{u} //
      cardinal.sum (λ a : α, c ^ cardinal.mk.{u} (β a)) ≤ c }
    ⟨⟨cardinal.mk (W_type β), le_of_eq cardinal_mk_eq_sum.symm⟩⟩
    (subtype.val) :=
le_antisymm
  (cardinal.le_min.2
    begin
      rintros ⟨i, hi⟩,
      dsimp only,
      conv_rhs { rw ← cardinal.mk_out i },
      rw [← cardinal.mk_out i] at hi,
      simp only [cardinal.power_def, cardinal.sum_mk, cardinal.le_def] at hi,
      cases hi,
      refine cardinal.mk_le_of_injective (to_type_injective _ _ _),
      { exact λ a f, hi ⟨a, f⟩ },
      { intros a₁ a₂ f₁ f₂,
        apply hi.2 }
    end)
  begin
    show _ ≤ (⟨cardinal.mk (W_type β), le_of_eq cardinal_mk_eq_sum.symm⟩ :
      { c : cardinal.{u} //
        cardinal.sum (λ a : α, c ^ cardinal.mk.{u} (β a)) ≤ c }).val,
    exact min_le _ _
  end




#exit

/-- The depth of a finitely branching tree. -/
noncomputable def depth' : W_type.{u u} β → ordinal.{u}
| ⟨a, f⟩ := ordinal.succ.{u} (ordinal.sup.{u u} (λ b : β a, depth' (f b)))



lemma depth'_pos (t : W_type β) : 0 < t.depth' :=
by { cases t, apply ordinal.succ_pos }

lemma depth'_lt_depth'_mk (a : α) (f : β a → W_type β) (i : β a) :
  depth' (f i) < depth' ⟨a, f⟩ :=
begin
  rw [depth', ordinal.lt_succ],
  exact ordinal.le_sup _ _
end

@[reducible] private def W_type' {α : Type u} (β : α → Type u) (n : ordinal.{u}) :=
{ t : W_type β // t.depth' ≤ n}

def consts : Type* := W_type' β 0

private def f (n : ordinal) : W_type' β n.succ → Σ a : α, β a → W_type' β n
| ⟨t, h⟩ :=
  begin
    cases t with a f,
    have h₀ : ∀ i : β a, W_type.depth' (f i) ≤ n,
      from λ i, ordinal.lt_succ.1 (lt_of_lt_of_le (W_type.depth'_lt_depth'_mk a f i) h),
    exact ⟨a, λ i : β a, ⟨f i, h₀ i⟩⟩
  end
#print sum_le_sup
private def finv (n : ordinal) :
  (Σ a : α, β a → W_type' β n) → W_type' β n.succ
| ⟨a, f⟩ :=
  begin
    let f' := λ i : β a, (f i).val,
    have : W_type.depth' ⟨a, f'⟩ ≤ n.succ,
      { rw [depth', ordinal.succ_le_succ, ordinal.sup_le],
        intro b,
        exact (f b).2 },
    exact ⟨⟨a, f'⟩, this⟩
  end

lemma f_injective (n : ordinal) : function.injective (@f α β n) :=
function.left_inverse.injective
  (show function.left_inverse (finv n) (f n),
    by { rintro ⟨⟨_, _⟩, _⟩, refl })

private def succ_le_cardinal (n : ordinal.{u}) (c : cardinal.{u})
  (h : cardinal.mk.{u} (W_type' β n) ≤ c) :
  cardinal.mk.{u} (W_type' β n.succ) ≤ cardinal.sum.{u u}
    (λ a : α, cardinal.mk (W_type' β n) ^ (cardinal.mk (β a))) :=
begin
  simp only [cardinal.power_def.{u}, cardinal.sum_mk],
  exact cardinal.mk_le_of_injective (f_injective.{u} n),
end

end W_type
