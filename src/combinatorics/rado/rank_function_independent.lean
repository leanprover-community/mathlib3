/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import combinatorics.rado.rank_function

/-!
# Independent families with respect to a rank function

Fix a rank function `r` on `α`. A family `f : ι → α` is *independent* on a finite set `s`
(with respect to `r`) if the rank of `f '' s` is (at least) the cardinality of `s`.
`f` is *independent* (with respect to `r`), if `f` is independent on any finite set `s`.

We define these notions (see `rank_fn.independent` and `rank_fn.independent_on`)
and provide some API lemmas.
-/

namespace rank_fn

open finset

variables {ι : Type*} {α : Type*} [decidable_eq α]

/-- A function `f : ι → α` is independent on a finset `s` (with respect to a rank function
`r` on `α`) if the image of `s` under `f` has rank equal to the cardinality of `s`.
(In the definition, we use `≤` instead of `=`, since this is easier to work with; the opposite
inequality is always true; see `rank_fn.independen_on.card_eq_rank_image`.) -/
def independent_on (r : rank_fn α) (f : ι → α) (s : finset ι) : Prop := s.card ≤ r (s.image f)

lemma independent_on_def {r : rank_fn α} {f : ι → α} {s : finset ι} :
  independent_on r f s ↔ s.card ≤ r (s.image f) := iff.rfl

lemma independent_on.card_eq_rank_image {r : rank_fn α}{f : ι → α} {s : finset ι}
  (h : independent_on r f s) : s.card = r (s.image f) :=
le_antisymm h ((r.le_card _).trans card_image_le)

lemma independent_on.congr {r : rank_fn α} {f g : ι → α} {s : finset ι}
  (hf : independent_on r f s) (h : set.eq_on f g ↑s) : independent_on r g s :=
le_of_le_of_eq hf $ congr_arg _ $ image_congr h

/-- A function `f : ι → α` is independent (with respect to a rank function `r` on `α`)
if `f` is independent on every finset `s`. -/
def independent (r : rank_fn α) (f : ι → α) : Prop := ∀ s : finset ι, independent_on r f s

/-- If `f` is independent on `s` with respect to the rank function `r` and `r'` is another
rank function such that `r ≤ r'`, then `f` is also independent on `s` with respect to `r'`. -/
lemma independent_on.mono {r r' : rank_fn α} (hr : r ≤ r') {f : ι → α} {s : finset ι}
  (hf : independent_on r f s) : independent_on r' f s :=
le_trans hf $ hr _

/-- If `f` is independent with respect to the rank function `r` and `r'` is another rank
function such that `r ≤ r'`, then `f` is also independent with respect to `r'`. -/
lemma independent.mono {r r' : rank_fn α} (hr : r ≤ r') {f : ι → α} (hf : independent r f) :
  independent r' f :=
λ s, (hf s).mono hr

variables {r : rank_fn α} {f : ι → α}

/-- A function is independent with respect to cardinality if and only if it is injective. -/
lemma independent_card_iff_injective : independent (card_rk α) f ↔ function.injective f :=
begin
  classical,
  refine ⟨λ H i j h, _, λ H s, (card_image_of_injective _ H).symm.le⟩,
  replace H := le_antisymm (H {i, j}) ((card_rk_eq_card (image f {i, j})).symm ▸ card_image_le),
  rw [card_rk_eq_card, image_insert, h, image_singleton, pair_eq_singleton, card_singleton] at H,
  refine (eq_or_ne i j).elim id (λ hh, by {cases (card_doubleton hh).symm.trans H,}),
end

/-- A function is independent on `s` with respect to cardinality if and only if
it is injective on `s`. -/
lemma independent_on_card_iff_inj_on {s : finset ι} :
  independent_on (card_rk α) f s ↔ set.inj_on f ↑s :=
⟨λ H, card_image_iff.mp $ le_antisymm card_image_le H, λ H, (card_image_of_inj_on H).symm.le⟩

/-- If `f` is independent, then `f` is injective. -/
lemma independent.injective (h : independent r f) : function.injective f :=
independent_card_iff_injective.mp $ h.mono r.le_card_rk

/-- If `f` is independent on `s`, then `f` is injective on `s`. -/
lemma independent_on.inj_on {s : finset ι} (h : independent_on r f s) : set.inj_on f ↑s :=
independent_on_card_iff_inj_on.mp $ h.mono r.le_card_rk

/-- If `f` is independent on `t`, then it is independent on every subset `s` of `t`. -/
lemma independent_on.subset {s t : finset ι} (h : independent_on r f t) (hst : s ⊆ t) :
  independent_on r f s :=
begin
  dsimp only [independent_on],
  convert r.card_le_subset (card_image_le.trans h) (image_subset_image hst),
  exact (card_image_iff.mpr $ set.inj_on.mono hst h.inj_on).symm,
end

/-- `f` is independent on `s` if and only if the restriction of `f` to `s`
is independent. -/
lemma independent_on_iff_independent_restrict {s : finset ι} :
  independent_on r f s ↔ independent r (set.restrict ↑s f) :=
begin
  classical,
  refine ⟨λ H t, _, λ H, _⟩,
  { rw [independent_on_def, image_restrict_eq_image_image_coe,
        ← card_image_iff.mpr $ set.inj_on_of_injective subtype.coe_injective _],
    have hts : (image coe t) ⊆ s,
    { convert image_subset_image (subset_univ t),
      simp only [univ_eq_attach, attach_image_coe], },
    exact H.subset hts, },
  { simpa only [independent_on_def, image_restrict_eq_image_image_coe, univ_eq_attach,
                attach_image_coe, card_attach] using H univ, }
end

end rank_fn
