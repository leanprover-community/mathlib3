import data.equiv.basic
import control.equiv_functor
/-!
# Equivalences for `option α`
-/

namespace equiv

variables {α β : Type*} (e : option α ≃ option β)

private def remove_none_aux (x : α) : β :=
if h : (e (some x)).is_some
  then option.get h
  else option.get $ show (e none).is_some, from
  begin
    rw ←option.ne_none_iff_is_some,
    intro hn,
    rw [option.not_is_some_iff_eq_none, ←hn] at h,
    simpa only using e.injective h,
  end

private lemma remove_none_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
  some (remove_none_aux e x) = e (some x) :=
by simp [remove_none_aux, option.is_some_iff_exists.mpr h]

private lemma remove_none_aux_none {x : α} (h : e (some x) = none) :
  some (remove_none_aux e x) = e none :=
by simp [remove_none_aux, option.not_is_some_iff_eq_none.mpr h]

private lemma remove_none_aux_inv (x : α) : remove_none_aux e.symm (remove_none_aux e x) = x :=
option.some_injective _ begin
  cases h1 : e.symm (some (remove_none_aux e x)); cases h2 : (e (some x)),
  { rw remove_none_aux_none _ h1,
    exact (e.eq_symm_apply.mpr h2).symm },
  { rw remove_none_aux_some _ ⟨_, h2⟩ at h1,
    simpa using h1, },
  { rw remove_none_aux_none _ h2 at h1,
    simpa using h1, },
  { rw remove_none_aux_some _ ⟨_, h1⟩,
    rw remove_none_aux_some _ ⟨_, h2⟩,
    simp },
end

/-- Given an equivalence between two `option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def remove_none : α ≃ β :=
{ to_fun := remove_none_aux e,
  inv_fun := remove_none_aux e.symm,
  left_inv := remove_none_aux_inv e,
  right_inv := remove_none_aux_inv e.symm, }

@[simp]
lemma remove_none_symm : (remove_none e).symm = remove_none e.symm := rfl

lemma remove_none_some {x : α} (h : ∃ x', e (some x) = some x') :
  some (remove_none e x) = e (some x) := remove_none_aux_some e h

lemma remove_none_none {x : α} (h : e (some x) = none) :
  some (remove_none e x) = e none := remove_none_aux_none e h

@[simp]
lemma remove_none_map_equiv {α β : Type*} (e : α ≃ β) :
  remove_none (equiv_functor.map_equiv option e) = e :=
equiv.ext $ λ x, option.some_injective _ $ remove_none_some _ ⟨e x, by simp [equiv_functor.map]⟩

end equiv
