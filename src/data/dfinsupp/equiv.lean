import data.dfinsupp.basic
import data.finset.preimage

namespace dfinsupp
open finset
universes u v u'
variables {ι : Type u} {κ : Type u'} {β : ι → Type v} [Π i, has_zero (β i)]

instance [is_empty ι] : unique (Π₀ i, β i) :=
⟨⟨0⟩, λ a, by { ext, exact is_empty_elim i }⟩

variables [decidable_eq ι] [decidable_eq κ] [Π i (x : β i), decidable (x ≠ 0)]
noncomputable def congr_left (h : κ → ι) (hh : function.injective h) :
(Π₀ i, β i) → (Π₀ k, β (h k)) :=
λ f, @mk _ (λ _, β _) _ _ (f.support.preimage h $ hh.inj_on _) (λ i, f (h i))

@[simp] lemma congr_left_apply (h : κ → ι) (hh : function.injective h) (f : Π₀ i, β i) (k : κ) :
congr_left h hh f k = f (h k) :=
begin
  dunfold congr_left, by_cases h0 : f (h k) = 0,
  { rw [h0, mk_of_not_mem], rw [mem_preimage, mem_support_to_fun, not_ne_iff, h0] },
  { apply mk_of_mem, rw [mem_preimage, mem_support_to_fun], exact h0 }
end

noncomputable def congr_left_equiv (h : ι ≃ κ) : (Π₀ i, β i) ≃ (Π₀ k, β (h.symm k)) :=
⟨congr_left h.symm h.symm.injective,
λ f, map_range (λ i, equiv.cast $ congr_arg β $ h.symm_apply_apply i)
  (λ i, (equiv.cast_eq_iff_heq _).mpr $
    by { convert heq.rfl, repeat { exact (h.symm_apply_apply i).symm } })
  (@congr_left _ _ _ _ _ _ _ h h.injective f),
λ f, by { ext i, rw [map_range_apply, congr_left_apply, congr_left_apply,
  equiv.cast_eq_iff_heq, h.symm_apply_apply] },
λ f, by { ext k, rw [congr_left_apply, map_range_apply, congr_left_apply,
  equiv.cast_eq_iff_heq, h.apply_symm_apply] }⟩

@[simp] lemma congr_left_equiv_apply (h : ι ≃ κ) (f : Π₀ i, β i) (k : κ) :
congr_left_equiv h f k = f (h.symm k) := congr_left_apply h.symm h.symm.injective f k

section curry
variables {α : ι → Type u'} {δ : (Σ i, α i) → Type v} [Π i, has_zero (δ i)]
[Π i, decidable_eq (α i)] [Π i (x : δ i), decidable (x ≠ 0)]

/--The natural map between `Π₀ (i : Σ i, α i), δ i` and `Π₀ i (j : α i), δ ⟨i, j⟩`.-/
noncomputable def curry (f : Π₀ i, δ i) : Π₀ i j, δ ⟨i, j⟩ :=
mk (f.support.image $ λ i, i.1)
  (λ i, mk (f.support.preimage (sigma.mk i) $ sigma_mk_injective.inj_on _) $ λ j, f ⟨i, j⟩)

@[simp] lemma curry_apply (f : Π₀ i, δ i) (i : ι) (j : α i) : curry f i j = f ⟨i, j⟩ :=
begin
  dunfold curry, by_cases h : f ⟨i, j⟩ = 0,
  { rw [h, mk_apply], split_ifs, { rw mk_apply, split_ifs, { exact h }, { refl } }, { refl } },
  { rw [mk_of_mem, mk_of_mem], { refl },
    { rw [mem_preimage, mem_support_to_fun], exact h },
    { rw mem_image, refine ⟨⟨i, j⟩, _, rfl⟩, rw mem_support_to_fun, exact h } }
end

variables [Π (i : ι) (f : Π₀ (j : α i), δ ⟨i, j⟩), decidable (f ≠ 0)]
/--The natural map between `Π₀ i (j : α i), δ ⟨i, j⟩` and `Π₀ (i : Σ i, α i), δ i`, inverse of
`curry`.-/
def uncurry (f : Π₀ i j, δ ⟨i, j⟩) : Π₀ i, δ i :=
mk (f.support.bUnion $ λ i, (f i).support.image $ sigma.mk i) (λ ⟨⟨i, j⟩, _⟩, f i j)

@[simp] lemma uncurry_apply (f : Π₀ i j, δ ⟨i, j⟩) (i : ι) (j : α i) : uncurry f ⟨i, j⟩ = f i j :=
begin
  dunfold uncurry, by_cases h : f i j = 0,
  { rw mk_apply, split_ifs, { refl }, { exact h.symm } },
  { apply mk_of_mem, rw mem_bUnion, refine ⟨i, _, _⟩,
    { rw mem_support_to_fun, intro H, rw ext_iff at H, exact h (H j) },
    { apply mem_image_of_mem, rw mem_support_to_fun, exact h } }
end

/--The natural bijection between `Π₀ (i : Σ i, α i), δ i` and `Π₀ i (j : α i), δ ⟨i, j⟩`.-/
noncomputable def curry_equiv : (Π₀ i, δ i) ≃ Π₀ i j, δ ⟨i, j⟩ := ⟨curry, uncurry,
λ f, by { ext ⟨i, j⟩, rw [uncurry_apply, curry_apply] },
λ f, by { ext i j, rw [curry_apply, uncurry_apply] }⟩

end curry

variables {α : option ι → Type v} [Π i, has_zero (α i)] [Π i (x : α i), decidable (x ≠ 0)]

noncomputable def remove_none (f : Π₀ i, α i) : Π₀ i, α (some i) :=
mk (f.support.preimage some $ (option.some_injective _).inj_on _) $ λ i, f $ some i
@[simp] lemma remove_none_apply (f : Π₀ i, α i) (i : ι) : remove_none f i = f (some i) :=
begin
  by_cases h : f (some i) = 0,
  { rw h, apply mk_of_not_mem, rw [mem_preimage, mem_support_to_fun, not_ne_iff, h] },
  { apply mk_of_mem, rw [mem_preimage, mem_support_to_fun], exact h }
end

def extend_with (f : Π₀ i, α (some i)) (a : α none) : Π₀ i, α i :=
mk (insert none $ f.support.image some) $ λ i, option.rec a f (i : option ι)
@[simp] lemma extend_with_none (f : Π₀ i, α (some i)) (a : α none) : f.extend_with a none = a :=
mk_of_mem $ mem_insert_self _ _
@[simp] lemma extend_with_some (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
f.extend_with a (some i) = f i :=
begin
  by_cases h : f i = 0,
  { rw h, apply mk_of_not_mem, simp only [mem_insert, mem_image, mem_support_to_fun, exists_prop,
    exists_eq_right, false_or, not_not], exact h },
  { exact (mk_of_mem $ mem_insert_of_mem $ mem_image_of_mem _ $ (mem_support_to_fun _ _).mpr h) }
end

@[simps] noncomputable def equiv_prod_dfinsupp : (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) :=
⟨λ f, (f none, f.remove_none), λ f, f.2.extend_with f.1,
λ f, begin ext i, cases i with i,
  { rw extend_with_none }, { rw [extend_with_some, remove_none_apply] } end,
λ _, begin ext, { exact extend_with_none _ _ }, { rw [remove_none_apply, extend_with_some] } end⟩

end dfinsupp
