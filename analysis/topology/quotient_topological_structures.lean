import analysis.topology.topological_structures
import group_theory.quotient_group

open function set

variables {α : Type*} [topological_space α] {β : Type*} [topological_space β]
variables {γ : Type*} [topological_space γ] {δ : Type*} [topological_space δ]

def is_open_map (f : α → β) := ∀ U : set α, is_open U → is_open (f '' U)

lemma is_open_map_iff_nhds_sets (f : α → β) : is_open_map f ↔ ∀(a:α) (U ∈(nhds a).sets), f '' U ∈(nhds (f a)).sets :=
begin
  split,
  { intros H a U U_nhd,
    rw mem_nhds_sets_iff at *,
    rcases U_nhd with ⟨s, s_sub, ⟨s_op, a_in_s⟩⟩,
    existsi [f '' s, image_subset _ s_sub],
    exact ⟨H s s_op, mem_image_of_mem _ a_in_s⟩ },
  { intros H U U_op,
    rw is_open_iff_mem_nhds,
    rintros b ⟨a, a_in, fa⟩,
    rw ←fa,
    exact H _ _ (mem_nhds_sets U_op a_in) }
end

lemma is_open_map_iff_nhds_le (f : α → β) : is_open_map f ↔ ∀(a:α), nhds (f a) ≤ (nhds a).map f :=
begin
  rw [is_open_map_iff_nhds_sets],
  refine forall_congr (assume a, _),
  split,
  exact assume h s hs, let ⟨t, ht, hts⟩ := filter.mem_map_sets_iff.1 hs in
    filter.mem_sets_of_superset (h t ht) hts,
  exact assume h u hu, h (filter.image_mem_map hu)
end

namespace is_open_map
protected lemma prod {f : α → β} {g : γ → δ} (hf : is_open_map f) (hg : is_open_map g) :
  is_open_map (λ p : α × γ, (f p.1, g p.2)) :=
begin
  rw [is_open_map_iff_nhds_le],
  rintros ⟨a, b⟩,
  rw [nhds_prod_eq, nhds_prod_eq, ← filter.prod_map_map_eq],
  exact filter.prod_mono ((is_open_map_iff_nhds_le f).1 hf a) ((is_open_map_iff_nhds_le g).1 hg b)
end

lemma of_inverse {f : α → β} {g : β → α} (h : continuous g) (l_inv : left_inverse f g) (r_inv : right_inverse f g) :
  is_open_map f :=
begin
  intros s s_op,
  have : f '' s = g ⁻¹' s,
  { ext x,
    simp [mem_image_iff_of_inverse r_inv l_inv] },
  rw this,
  exact h s s_op
end

local attribute [extensionality] topological_space_eq
open function
lemma quotient_map_of_open_of_surj_of_cont {f : α → β} (cont : continuous f) (op : is_open_map f) (surj : surjective f): quotient_map f :=
⟨surj, begin
  ext s,
  split; intro h,
  { exact cont s h },
  have := op (f ⁻¹' s) h,
  rwa image_preimage_eq surj at this,
end⟩
end is_open_map

class topological_group (α : Type*) [topological_space α] [group α]
  extends topological_monoid α : Prop :=
(continuous_inv : continuous (λa:α, a⁻¹))

lemma continuous_inv' {α : Type*} [topological_space α] [group α] [topological_group α] :
continuous (λ a : α, a⁻¹) := topological_group.continuous_inv α

lemma continuous_inv {α : Type*} {β : Type*} [topological_space α] [group α] [topological_group α] [topological_space β] {f : β → α} (hf : continuous f) :
continuous (λ b, (f b)⁻¹) := hf.comp continuous_inv'

section topological_group
variables [group α] [topological_group α] (N : set α) [normal_subgroup N]

instance : topological_space (quotient_group.quotient N) :=
by dunfold quotient_group.quotient ; apply_instance

open quotient_group
lemma quotient_group_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, y*x.1) '' s) :=
begin
  ext x,
  rw mem_preimage_eq,
  rw mem_Union,
  split ; intro h,
  { rcases h with ⟨a, a_in, h⟩,
    rw quotient_group.eq at h,
    existsi (⟨a⁻¹*x, h⟩ : N),
    rw mem_image,
    existsi [a, a_in],
    simp },
  { rcases h with ⟨⟨n, n_in⟩, x_in⟩,
    rw mem_image at x_in,
    rcases x_in with ⟨a, a_in, ha⟩,
    rw mem_image,
    existsi [a, a_in],
    rw quotient_group.eq,
    rwa show a⁻¹*x = n, by rw ←ha ; simp }
end

lemma is_open_translate (a : α) : is_open_map (λ x, x*a) :=
begin
  have : continuous (λ x, x*a⁻¹) := continuous_mul continuous_id continuous_const,
  apply is_open_map.of_inverse this,
  simp[function.left_inverse],
  intro x, simp,
end

lemma quotient_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_translate n s s_op
end

instance topological_group_quotient : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
    continuous.comp continuous_mul' continuous_quot_mk,

    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.quotient_map_of_open_of_surj_of_cont,
      { apply continuous.prod_mk,
        { exact continuous.comp continuous_fst continuous_quot_mk },
        { exact continuous.comp continuous_snd continuous_quot_mk } },
      { exact is_open_map.prod (quotient_group.open_coe N) (quotient_group.open_coe N) },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        existsi (x, y),
        refl }},
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), a⁻¹)),
    exact continuous.comp continuous_inv' continuous_quot_mk
  end }
end topological_group

section topological_add_group
variables [add_comm_group α] [topological_add_group α] (N : set α) [is_add_subgroup N]

instance [topological_add_group α] (N : set α) [is_add_subgroup N]: topological_space (quotient_add_group.quotient N) :=
by dunfold quotient_add_group.quotient ; apply_instance

open quotient_add_group

lemma quotient_add_group_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  rw mem_preimage_eq,
  rw mem_Union,
  split ; intro h,
  { rcases h with ⟨a, a_in, h⟩,
    rw quotient_add_group.eq at h,
    existsi (⟨-a+x, h⟩ : N),
    rw mem_image,
    existsi [a, a_in],
    simp },
  { rcases h with ⟨⟨n, n_in⟩, x_in⟩,
    rw mem_image at x_in,
    rcases x_in with ⟨a, a_in, ha⟩,
    rw mem_image,
    existsi [a, a_in],
    rw quotient_add_group.eq,
    rwa show -a + x = n, by rw ←ha ; simp }
end

lemma is_open_add_translate (a : α) : is_open_map (λ x, a + x) :=
begin
  have : continuous (λ x, -a + x) := continuous_add continuous_const continuous_id,
  apply is_open_map.of_inverse this,
  simp[function.left_inverse], intro x, rw [add_comm, add_assoc], simp,
  simp[function.left_inverse], intro x, finish
end

lemma quotient_add_group.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_add_group_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_add_translate n s s_op
end

instance topological_add_group_quotient : topological_add_group (quotient N) :=
{ continuous_add := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst + p.snd)) :=
    continuous.comp continuous_add' continuous_quot_mk,

    have quot : quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.quotient_map_of_open_of_surj_of_cont,
      { apply continuous.prod_mk,
        { exact continuous.comp continuous_fst continuous_quot_mk },
        { exact continuous.comp continuous_snd continuous_quot_mk } },
      { exact is_open_map.prod (quotient_add_group.open_coe N) (quotient_add_group.open_coe N) },
      { rintro ⟨⟨x⟩, ⟨y⟩⟩,
        existsi (x, y),
        refl }},
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_neg := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), -a)),
    exact continuous.comp continuous_neg' continuous_quot_mk
  end }
end topological_add_group

section ideal_is_add_subgroup
variables [comm_ring α] {M : Type*} [module α M] (N : set α) [is_submodule N]

instance submodule_is_add_subgroup : is_add_subgroup N :=
{ zero_mem :=  is_submodule.zero,
  add_mem :=  λ a b, is_submodule.add,
  neg_mem := λ a,  is_submodule.neg}
end ideal_is_add_subgroup

section topological_ring
variables [comm_ring α] [topological_ring α] (N : set α) [is_ideal N]
open quotient_ring

instance topological_ring_quotient_topology : topological_space (quotient N) :=
by dunfold quotient_ring.quotient ; apply_instance

lemma is_open_ring_add_translate (a : α) : is_open_map (λ x, a + x) :=
begin
  have : continuous (λ x, -a + x) := continuous_add continuous_const continuous_id,
  apply is_open_map.of_inverse this,
  simp[function.left_inverse], intro x, rw [add_comm, add_assoc], simp,
  simp[function.left_inverse], intro x, change a + x - a = x, ring
end

lemma quotient_ring_saturate (s : set α) :
  (coe : α → quotient N) ⁻¹' ((coe : α → quotient N) '' s) = (⋃ x : N, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  rw mem_preimage_eq,
  rw mem_Union,
  split ; intro h,
  { rcases h with ⟨a, a_in, h⟩,
    rw [quotient_ring.eq, @is_ideal.neg_iff _ _ _ N _,
        show -(a-x) = -a + x, by {ring}] at h,
    existsi (⟨-a+x, h⟩ : N),
    rw mem_image,
    existsi [a, a_in],
    simp },
  { rcases h with ⟨⟨n, n_in⟩, x_in⟩,
    rw mem_image at x_in,
    rcases x_in with ⟨a, a_in, ha⟩,
    rw mem_image,
    existsi [a, a_in],
    rw quotient_ring.eq,
    rw @is_ideal.neg_iff _ _ _ N _,
    rwa show -(a - x) = n, by {rw ←ha, simp} }
end

lemma quotient_ring.open_coe : is_open_map (coe : α →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : α →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_ring_saturate N s,
  apply is_open_Union,
  rintro ⟨n, _⟩,
  exact is_open_ring_add_translate n s s_op
end

lemma quotient_ring.is_open_map :quotient_map (λ p : α × α, ((p.1:quotient N), (p.2:quotient N))) :=
begin
  apply is_open_map.quotient_map_of_open_of_surj_of_cont,
  { apply continuous.prod_mk,
    { exact continuous.comp continuous_fst continuous_quot_mk },
    { exact continuous.comp continuous_snd continuous_quot_mk } },
  { exact is_open_map.prod (quotient_ring.open_coe N) (quotient_ring.open_coe N) },
  { rintro ⟨⟨x⟩, ⟨y⟩⟩,
    existsi (x, y),
    refl }
end

instance topological_ring_quotient : topological_ring (quotient N) :=
{continuous_add := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst + p.snd)) :=
    continuous.comp continuous_add' continuous_quot_mk,
    exact (quotient_map.continuous_iff (quotient_ring.is_open_map N)).2 cont,
  end,
  continuous_neg := begin
    apply continuous_quotient_lift,
    change continuous ((coe : α → quotient N) ∘ (λ (a : α), -a)),
    exact continuous.comp continuous_neg' continuous_quot_mk
  end,
  continuous_mul := begin
    have cont : continuous ((coe : α → quotient N) ∘ (λ (p : α × α), p.fst * p.snd)) :=
    continuous.comp continuous_mul' continuous_quot_mk,
    exact (quotient_map.continuous_iff (quotient_ring.is_open_map N)).2 cont
  end}
end topological_ring