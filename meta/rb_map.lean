/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

Additional operations on native rb_maps and rb_sets.
-/

namespace native
namespace rb_set 

meta def filter {key} (s : rb_set key) (P : key → bool) : rb_set key :=
s.fold s (λ a m, if P a then m else m.erase a)

meta def union {key} (s t : rb_set key) : rb_set key :=
s.fold t (λ a t, t.insert a)

end rb_set 

namespace rb_map 

meta def ifind {α β} [inhabited β] (m : rb_map α β) (a : α) : β :=
match m.find a with 
| some a := a 
| none := default β
end 

meta def zfind {α β} [has_zero β] (m : rb_map α β) (a : α) : β :=
match m.find a with 
| some v := v 
| none := 0
end

meta def add {α β} [has_add β] [has_zero β] [decidable_eq β] (m1 m2 : rb_map α β) : rb_map α β :=
m1.fold m2 
  (λ n v m, 
   let nv := v + m2.zfind n in
   if nv = 0 then m.erase n else m.insert n nv)

meta def scale {α β} [has_lt α] [decidable_rel ((<) : α → α → Prop)] [has_mul β] (b : β) (m : rb_map α β) : rb_map α β :=
m.map ((*) b)

end rb_map 
end native