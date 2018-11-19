/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Additional operations on native rb_maps and rb_sets.
-/
import data.option

namespace native
namespace rb_set

meta def filter {key} (s : rb_set key) (P : key → bool) : rb_set key :=
s.fold s (λ a m, if P a then m else m.erase a)

meta def union {key} (s t : rb_set key) : rb_set key :=
s.fold t (λ a t, t.insert a)

end rb_set

namespace rb_map

meta def find_def {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
  (x : β) (m : rb_map α β) (k : α) :=
(m.find k).get_or_else x

meta def insert_cons {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
  (k : α) (x : β) (m : rb_map α (list β)) : rb_map α (list β) :=
m.insert k (x :: m.find_def [] k)

meta def ifind {α β} [inhabited β] (m : rb_map α β) (a : α) : β :=
(m.find a).iget

meta def zfind {α β} [has_zero β] (m : rb_map α β) (a : α) : β :=
(m.find a).get_or_else 0

meta def add {α β} [has_add β] [has_zero β] [decidable_eq β] (m1 m2 : rb_map α β) : rb_map α β :=
m1.fold m2
  (λ n v m,
   let nv := v + m2.zfind n in
   if nv = 0 then m.erase n else m.insert n nv)

meta def scale {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)] [has_mul β] (b : β) (m : rb_map α β) : rb_map α β :=
m.map ((*) b)

section
open format prod
variables {key : Type} {data : Type} [has_to_tactic_format key] [has_to_tactic_format data]
private meta def pp_key_data (k : key) (d : data) (first : bool) : tactic format :=
do fk ← tactic.pp k, fd ← tactic.pp d, return $
(if first then to_fmt "" else to_fmt "," ++ line) ++ fk ++ space ++ to_fmt "←" ++ space ++ fd

meta instance : has_to_tactic_format (rb_map key data) :=
⟨λ m, do
  (fmt, _) ← fold m (return (to_fmt "", tt))
     (λ k d p, do p ← p, pkd ← pp_key_data k d (snd p), return (fst p ++ pkd, ff)),
  return $ group $ to_fmt "⟨" ++ nest 1 fmt ++ to_fmt "⟩"⟩
end

end rb_map
end native
