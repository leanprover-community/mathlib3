import order.complete_lattice

instance fixed_points_complete_lattice {α : Type*} [complete_lattice α] {f : α → α} [monotone f] :
complete_lattice {x // x = f x} :=
{ le := (≤),
  top := ⟨(⨆ (x : α) (hx : x ≤ f x), x), begin
    let u := ⨆ (x : α) (hx : x ≤ f x), x,
    have h : u ≤ f u := bsupr_le (λ x hx, hx.trans (‹monotone f› (le_bsupr x hx))),
    refine h.antisymm _,
    apply le_bsupr_of_le _,--exact le_bsupr (f u) (‹monotone f› h), weirdly doesn't work
    exact ‹monotone f› h,
    exact le_refl _,
  end⟩,
  le_top := λ ⟨x, hx⟩, begin
    apply le_bsupr_of_le,
    exact hx.le,
    exact le_refl _,
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
  .. @complete_lattice_of_complete_semilattice_Sup {x // x = f x}
  { le := (≤),
    le_refl := le_refl,
    le_trans := λ x y z, le_trans,
    le_antisymm := λ x y, le_antisymm,
    Sup := λ s, ⟨(⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x), begin
      let u := (⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x),
      have h : f u ≤ u,
      refine le_binfi (λ x hx, le_infi (λ hxs, le_trans (‹monotone f› _) hx)),
      apply binfi_le_of_le,
      exact hx,
      exact infi_le _ hxs,
      refine (h.antisymm _).symm,
      apply binfi_le_of_le (f u) _ _,
      exact (‹monotone f› h),
      apply infi_le,
      rintro ⟨y, hy⟩ hys,
      refine hy.le.trans (‹monotone f› _),
      apply le_binfi,
      rintro z hz,
      apply le_infi,
      rintro hzs,
      exact hzs ⟨y, hy⟩ hys,
    end⟩,
    le_Sup := λ s x hxs, begin
      apply le_binfi,
      rintro y hy,
      apply le_infi,
      rintro hys,
      exact hys x hxs,
    end,
    Sup_le := λ s ⟨x, hx⟩ hxs, begin
      apply binfi_le_of_le,
      exact hx.ge,
      apply infi_le,
      rintro y hy,
      exact hxs y hy,
    end }}
/-@complete_lattice_of_complete_semilattice_Sup {x // x = f x}
{ le := (≤),
  le_refl := le_refl,
  le_trans := λ x y z, le_trans,
  le_antisymm := λ x y, le_antisymm,
  Sup := λ s, ⟨(⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x), begin
    let u := (⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x),
    have h : f u ≤ u,
    refine le_binfi (λ x hx, le_infi (λ hxs, le_trans (‹monotone f› _) hx)),
    apply binfi_le_of_le,
    exact hx,
    exact infi_le _ hxs,
    refine (h.antisymm _).symm,
    apply binfi_le_of_le (f u) _ _,
    exact (‹monotone f› h),
    apply infi_le,
    rintro ⟨y, hy⟩ hys,
    refine hy.le.trans (‹monotone f› _),
    apply le_binfi,
    rintro z hz,
    apply le_infi,
    rintro hzs,
    exact hzs ⟨y, hy⟩ hys,
  end⟩,
  le_Sup := λ s x hxs, begin
    apply le_binfi,
    rintro y hy,
    apply le_infi,
    rintro hys,
    exact hys x hxs,
  end,
  Sup_le := λ s ⟨x, hx⟩ hxs, begin
    apply binfi_le_of_le,
    exact hx.ge,
    apply infi_le,
    rintro y hy,
    exact hxs y hy,
  end }-/
/-{ sup := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x ⊔ y, begin
    have h : x ⊔ y ≤ f (x ⊔ y) := sup_le (hx.le.trans (‹monotone f› (le_sup_left)))
      (hy.le.trans (‹monotone f› (le_sup_right))),
    refine h.antisymm _,
    refine le_trans (le_trans (‹monotone f› _) hx.ge) le_sup_left,
    apply le_sup_left.trans,
  end⟩,
  /-sup := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x ⊔ y, begin
    have h : x ⊔ y ≤ f (x ⊔ y) := sup_le (hx.le.trans (‹monotone f› (le_sup_left)))
      (hy.le.trans (‹monotone f› (le_sup_right))),
    refine h.antisymm _,
    refine le_trans (le_trans (‹monotone f› _) hx.ge) le_sup_left,
    apply le_sup_left.trans,
  end⟩,-/
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
  Sup := λ s, ⟨(⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x), begin
    let u := (⨅ (x : α) (hx : f x ≤ x) (hxs : ∀ y ∈ s, ↑y ≤ x), x),
    have h : f u ≤ u,
    refine le_binfi (λ x hx, le_infi (λ hxs, le_trans (‹monotone f› _) hx)),
    apply binfi_le_of_le,
    exact hx,
    exact infi_le _ hxs,
    refine (h.antisymm _).symm,
    apply binfi_le_of_le (f u) _ _,
    exact (‹monotone f› h),
    apply infi_le,
    rintro ⟨y, hy⟩ hys,
    refine hy.le.trans (‹monotone f› _),
    apply le_binfi,
    rintro z hz,
    apply le_infi,
    rintro hzs,
    exact hzs ⟨y, hy⟩ hys,
  end⟩,
  le_Sup := λ s x hxs, begin
    apply le_binfi,
    rintro y hy,
    apply le_infi,
    rintro hys,
    exact hys x hxs,
  end,
  Sup_le := λ s ⟨x, hx⟩ hxs, begin
    apply binfi_le_of_le,
    exact hx.ge,
    apply infi_le,
    rintro y hy,
    exact hxs y hy,
  end,
  Inf := λ s, ⟨(⨆ (x : α) (hx : x ≤ f x) (hxs : ∀ y ∈ s, x ≤ ↑y), x), begin
    sorry
  end⟩,
  Inf_le := λ s x hxs, begin
    apply bsupr_le,
    rintro y hy,
    apply supr_le,
    rintro hys,
    exact hys x hxs,
  end,
  le_Inf := λ s ⟨x, hx⟩ hxs, begin
    apply le_bsupr_of_le,
    exact hx.le,
    apply le_supr_of_le,
    rintro y hy,
    exact hxs y hy,
    exact le_refl _,
  end }-/
