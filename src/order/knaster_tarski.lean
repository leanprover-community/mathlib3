import order.complete_lattice

variables {α : Type*} [complete_lattice α] {f : α → α} [monotone f]

def fixed_points_complete_lattice :
complete_lattice {x // x = f x} :=
{ sup := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x ⊔ y, begin
    apply le_antisymm,
    apply sup_le,
    exact hx.le.trans (‹monotone f› (le_sup_left)),
    exact hy.le.trans (‹monotone f› (le_sup_right)),
    refine le_trans (le_trans (‹monotone f› _) hx.ge) le_sup_left,
    apply le_sup_left.trans,
  end⟩,
  le := (≤),
  le_refl := le_refl,
  le_trans := λ x y z, le_trans,
  le_antisymm := λ x y, le_antisymm,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,
  top := ⟨(⨆ (x : α) (hx : x ≤ f x), x), begin
    let u := ⨆ (x : α) (hx : x ≤ f x), x,
    have h : u ≤ f u := bsupr_le (λ x hx, hx.trans (‹monotone f› (le_bsupr x hx))),
    refine h.antisymm _,
    apply le_bsupr_of_le _,--exact le_bsupr (f u) (‹monotone f› h), weirdly doesn't work
    exact ‹monotone f› h,
    exact le_refl _,
  end⟩,
  le_top := λ ⟨x, hx⟩, begin
      sorry
  end,
  bot := ⟨(⨅ (x : α) (hx : f x ≤ x), x), begin
    let u := ⨅ (x : α) (hx : f x ≤ x), x,
    have h : f u ≤ u := le_binfi (λ x hx, le_trans (‹monotone f› (binfi_le x hx)) hx),
    refine (h.antisymm _).symm,
    exact binfi_le (f u) (‹monotone f› h),--and this works!!!
  end⟩,
  bot_le := λ ⟨x, hx⟩, begin
    refine binfi_le x _,
    exact hx.ge,
  end,
  Sup := λ s, ⟨(⨆ (x : {x // x = f x}) (hx : x ∈ s), x), begin
    let u := (⨆ (x : α) (hx : x = f x), x),
    have h : u ≤ f u := bsupr_le (λ x hx, hx.le.trans (‹monotone f› (le_bsupr x hx))),
  end⟩,
  le_Sup := _,
  Sup_le := _,
  Inf := _,
  Inf_le := _,
  le_Inf := _ }
