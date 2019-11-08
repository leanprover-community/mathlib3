import data.list.defs

import .ideas

namespace back
namespace brains

namespace queue

meta structure ideas :=
(first : thought)
(queue : list thought)

structure qpos :=
(pos : ℕ)

meta def startup (is : list idea) (cfg : config) : tactic ideas :=
do (first :: rest) ← is.mmap $ thought.of_idea cfg,
   return ⟨first, rest⟩

meta def init (i : ideas) (_ : expr) : tactic (thought × qpos) :=
return (i.first, ⟨0⟩)

meta def rethink (i : ideas) (g : goal qpos) : tactic (option (goal qpos)) :=
return $ (i.queue.nth g.mem.pos).map $ λ t, t.init ⟨g.mem.pos + 1⟩ g.mvar

end queue

section

open queue
meta def queue (is : list idea) : brain := ⟨startup is, init, rethink⟩

end

end brains
end back
