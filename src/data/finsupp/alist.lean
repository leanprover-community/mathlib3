/-
Copyright (c) 2022 Violeta Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández
-/
import data.finsupp.basic
import data.list.alist

/-!
# Connections between `finsupp` and `alist`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `finsupp.to_alist`
* `alist.lookup_finsupp`: converts an association list into a finitely supported function
  via `alist.lookup`, sending absent keys to zero.

-/

namespace finsupp
variables {α M : Type*} [has_zero M]

/-- Produce an association list for the finsupp over its support using choice. -/
@[simps] noncomputable def to_alist (f : α →₀ M) : alist (λ x : α, M) :=
⟨f.graph.to_list.map prod.to_sigma, begin
  rw [list.nodupkeys, list.keys, list.map_map, prod.fst_comp_to_sigma, list.nodup_map_iff_inj_on],
  { rintros ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c),
    rw [finset.mem_to_list, finsupp.mem_graph_iff] at hb hc,
    dsimp at hb hc,
    rw [←hc.1, hb.1] },
  { apply finset.nodup_to_list }
end⟩

@[simp] lemma to_alist_keys_to_finset [decidable_eq α] (f : α →₀ M) :
  f.to_alist.keys.to_finset = f.support :=
by { ext, simp [to_alist, alist.mem_keys, alist.keys, list.keys] }

@[simp] lemma mem_to_alist {f : α →₀ M} {x : α} : x ∈ f.to_alist ↔ f x ≠ 0 :=
begin
  classical,
  rw [alist.mem_keys, ←list.mem_to_finset, to_alist_keys_to_finset, mem_support_iff]
end

end finsupp

namespace alist
variables {α M : Type*} [has_zero M]
open list

/-- Converts an association list into a finitely supported function via `alist.lookup`, sending
absent keys to zero. -/
noncomputable def lookup_finsupp (l : alist (λ x : α, M)) : α →₀ M :=
{ support := by haveI := classical.dec_eq α; haveI := classical.dec_eq M; exact
    (l.1.filter $ λ x, sigma.snd x ≠ 0).keys.to_finset,
  to_fun := λ a, by haveI := classical.dec_eq α; exact (l.lookup a).get_or_else 0,
  mem_support_to_fun := λ a, begin
    classical,
    simp_rw [mem_to_finset, list.mem_keys, list.mem_filter, ←mem_lookup_iff],
    cases lookup a l;
    simp
  end }

@[simp] lemma lookup_finsupp_apply [decidable_eq α] (l : alist (λ x : α, M)) (a : α) :
  l.lookup_finsupp a = (l.lookup a).get_or_else 0 :=
by convert rfl

@[simp] lemma lookup_finsupp_support [decidable_eq α] [decidable_eq M] (l : alist (λ x : α, M)) :
  l.lookup_finsupp.support = (l.1.filter $ λ x, sigma.snd x ≠ 0).keys.to_finset :=
by convert rfl

lemma lookup_finsupp_eq_iff_of_ne_zero [decidable_eq α]
  {l : alist (λ x : α, M)} {a : α} {x : M} (hx : x ≠ 0) :
  l.lookup_finsupp a = x ↔ x ∈ l.lookup a :=
by { rw lookup_finsupp_apply, cases lookup a l with m; simp [hx.symm] }

lemma lookup_finsupp_eq_zero_iff [decidable_eq α] {l : alist (λ x : α, M)} {a : α} :
  l.lookup_finsupp a = 0 ↔ a ∉ l ∨ (0 : M) ∈ l.lookup a :=
by { rw [lookup_finsupp_apply, ←lookup_eq_none], cases lookup a l with m; simp }

@[simp] lemma empty_lookup_finsupp : lookup_finsupp (∅ : alist (λ x : α, M)) = 0 :=
by { classical, ext, simp }

@[simp] lemma insert_lookup_finsupp [decidable_eq α] (l : alist (λ x : α, M)) (a : α) (m : M) :
  (l.insert a m).lookup_finsupp = l.lookup_finsupp.update a m :=
by { ext b, by_cases h : b = a; simp [h] }

@[simp] lemma singleton_lookup_finsupp (a : α) (m : M) :
  (singleton a m).lookup_finsupp = finsupp.single a m :=
by { classical, simp [←alist.insert_empty] }

@[simp] lemma _root_.finsupp.to_alist_lookup_finsupp (f : α →₀ M) : f.to_alist.lookup_finsupp = f :=
begin
  ext,
  classical,
  by_cases h : f a = 0,
  { suffices : f.to_alist.lookup a = none,
    { simp [h, this] },
    { simp [lookup_eq_none, h] } },
  { suffices : f.to_alist.lookup a = some (f a),
    { simp [h, this] },
    { apply mem_lookup_iff.2,
      simpa using h } }
end

lemma lookup_finsupp_surjective : function.surjective (@lookup_finsupp α M _) :=
λ f, ⟨_, finsupp.to_alist_lookup_finsupp f⟩

end alist
