import tactic.local_cache

open tactic

def do_trace : bool := ff

meta def trace_cache_regenerating : tactic unit :=
if do_trace then trace "(test/local_cache): cache regenerating" else skip

namespace block_local

section example_tactic

def TEST_NS_1 : name := `my_tactic
def TEST_NS_2 : name := `my_other_tactic

-- Example "expensive" function
meta def generate_some_data : tactic (list ℕ) :=
do trace_cache_regenerating,
   return [1, 2, 3, 4]

meta def my_tactic : tactic unit :=
do my_cached_data ← run_once TEST_NS_1 generate_some_data,
   -- Do some stuff with `my_cached_data`
   skip

meta def my_other_tactic : tactic unit :=
run_once TEST_NS_2 (return [10, 20, 30, 40]) >> skip

end example_tactic



section example_usage

-- Note only a single cache regeneration (only a single trace message),
-- even upon descent to a sub-tactic-block.
lemma my_lemma : true := begin
    my_tactic,
    my_tactic,
    my_tactic,

    have h : true,
    { my_tactic,
      trivial },

    trivial
end

end example_usage

section test

meta def fail_if_cache_miss (ns : name) : tactic unit :=
do p ← local_cache.present ns,
   if p then skip else fail "cache miss"

meta def fail_if_cache_miss_1 : tactic unit :=
fail_if_cache_miss TEST_NS_1

meta def fail_if_cache_miss_2 : tactic unit :=
fail_if_cache_miss TEST_NS_2

end test

-- Test: the cache persists only within a single tactic block
section test_scope

structure dummy :=
(a b : ℕ)

def my_definition : dummy :=
 ⟨ begin
     my_tactic,
     fail_if_cache_miss_1,
     exact 1
   end,
   begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end, ⟩

def my_definition' : dummy :=
 ⟨ begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end,
   begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end, ⟩

noncomputable
lemma my_lemma' : dummy :=
 ⟨ begin
     my_tactic,
     fail_if_cache_miss_1,
     exact 1
   end,
   begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end, ⟩

end test_scope

-- Test: the cache is reliably persistent, decends to sub-blocks,
-- the api to inspect whether a cache entry is present works, and
-- the cache can be manually cleared.
section test_persistence

lemma my_test_ps : true := begin
  success_if_fail { fail_if_cache_miss_1 },

  my_tactic,

  fail_if_cache_miss_1,
  fail_if_cache_miss_1,
  success_if_fail { fail_if_cache_miss_2 },

  have h : true,
  { fail_if_cache_miss_1,
    trivial },

  -- Manually clear cache
  local_cache.clear TEST_NS_1,
  success_if_fail { fail_if_cache_miss_1 },

  trivial
end

end test_persistence

-- Test: caching under different namespaces doesn't share the
-- cached state.
section test_ns_collison

lemma my_test_ns : true := begin
  my_tactic,
  fail_if_cache_miss_1,
  success_if_fail { fail_if_cache_miss_2 },

  my_other_tactic,
  fail_if_cache_miss_1,
  fail_if_cache_miss_2,

  local_cache.clear TEST_NS_1,
  success_if_fail { fail_if_cache_miss_1 },
  fail_if_cache_miss_2,

  my_other_tactic,
  success_if_fail { fail_if_cache_miss_1 },
  fail_if_cache_miss_2,

  trivial
end

end test_ns_collison

-- Test: cached results don't leak between `def`s or `lemma`s.
section test_locality

def my_def_1 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

def my_def_2 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

lemma my_lemma_1 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

lemma my_lemma_2 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

end test_locality

-- Test: the `local_cache.get` function.
section test_get

meta def assert_equal {α : Type} [decidable_eq α] (a : α) (ta : tactic α) : tactic unit :=
do a' ← ta,
   if a = a' then skip
             else fail "not equal!"

lemma my_lemma_3 : true := begin
  assert_equal none (local_cache.get TEST_NS_1 (list ℕ)),

  my_tactic,
  my_other_tactic,
  assert_equal (some [1,2,3,4]) (local_cache.get TEST_NS_1 (list ℕ)),
  assert_equal (some [10, 20, 30, 40]) (local_cache.get TEST_NS_2 (list ℕ)),

  trivial
end

end test_get

end block_local



---------------------------
-- Now test again with the `def_local` scope.
---------------------------


namespace def_local

open tactic.local_cache.cache_scope

section example_tactic

def TEST_NS_1 : name := `my_tactic
def TEST_NS_2 : name := `my_other_tactic

-- Example "expensive" function
meta def generate_some_data : tactic (list ℕ) :=
do trace_cache_regenerating,
   return [1, 2, 3, 4]

meta def my_tactic : tactic unit :=
do my_cached_data ← run_once TEST_NS_1 generate_some_data def_local,
   -- Do some stuff with `my_cached_data`
   skip

meta def my_other_tactic : tactic unit :=
run_once TEST_NS_2 (return [10, 20, 30, 40]) def_local >> skip

end example_tactic



section example_usage

-- Note only a single cache regeneration (only a single trace message),
-- even upon descent to a sub-tactic-block.
lemma my_lemma : true := begin
    my_tactic,
    my_tactic,
    my_tactic,

    have h : true,
    { my_tactic,
      trivial },

    trivial
end

end example_usage

section test

meta def fail_if_cache_miss (ns : name) : tactic unit :=
do p ← local_cache.present ns def_local,
   if p then skip else fail "cache miss"

meta def fail_if_cache_miss_1 : tactic unit :=
fail_if_cache_miss TEST_NS_1

meta def fail_if_cache_miss_2 : tactic unit :=
fail_if_cache_miss TEST_NS_2

end test

-- Test: the cache really does persist over a whole definition
section test_scope

structure dummy :=
(a b : ℕ)

def my_definition : dummy :=
 ⟨ begin
     my_tactic,
     fail_if_cache_miss_1,
     exact 1
   end,
   begin
     fail_if_cache_miss_1,
     exact 1
   end, ⟩

def my_definition' : dummy :=
 ⟨ begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end,
   begin
     success_if_fail { fail_if_cache_miss_1 },
     exact 1
   end, ⟩

noncomputable
lemma my_lemma' : dummy :=
 ⟨ begin
     my_tactic,
     fail_if_cache_miss_1,
     exact 1
   end,
   begin
     fail_if_cache_miss_1,
     exact 1
   end, ⟩

end test_scope

-- Test: the cache is reliably persistent, decends to sub-blocks,
-- the api to inspect whether a cache entry is present works, and
-- the cache can be manually cleared.
section test_persistence

lemma my_test_ps : true := begin
  success_if_fail { fail_if_cache_miss_1 },

  my_tactic,
  my_tactic,

  fail_if_cache_miss_1,
  fail_if_cache_miss_1,
  success_if_fail { fail_if_cache_miss_2 },

  have h : true,
  { fail_if_cache_miss_1,
    trivial },

  -- Manually clear cache
  local_cache.clear TEST_NS_1 def_local,
  success_if_fail { fail_if_cache_miss_1 },

  trivial
end

end test_persistence

-- Test: caching under different namespaces doesn't share the
-- cached state.
section test_ns_collison

lemma my_test_ns : true := begin
  my_tactic,
  fail_if_cache_miss_1,
  success_if_fail { fail_if_cache_miss_2 },

  my_other_tactic,
  fail_if_cache_miss_1,
  fail_if_cache_miss_2,

  local_cache.clear TEST_NS_1 def_local,
  success_if_fail { fail_if_cache_miss_1 },
  fail_if_cache_miss_2,

  my_other_tactic,
  success_if_fail { fail_if_cache_miss_1 },
  fail_if_cache_miss_2,

  trivial
end

end test_ns_collison

-- Test: cached results don't leak between `def`s or `lemma`s.
section test_locality

def my_def_1 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

def my_def_2 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

lemma my_lemma_1 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

lemma my_lemma_2 : true := begin
  success_if_fail { fail_if_cache_miss_1 },
  my_tactic,
  fail_if_cache_miss_1,

  trivial
end

end test_locality

-- Test: the `local_cache.get` function.
section test_get

meta def assert_equal {α : Type} [decidable_eq α] (a : α) (ta : tactic α) : tactic unit :=
do a' ← ta,
   if a = a' then skip
             else fail "not equal!"

lemma my_lemma_3 : true := begin
  assert_equal none (local_cache.get TEST_NS_1 (list ℕ)),

  my_tactic,
  my_other_tactic,
  assert_equal (some [1,2,3,4]) (local_cache.get TEST_NS_1 (list ℕ) def_local),
  assert_equal (some [10, 20, 30, 40]) (local_cache.get TEST_NS_2 (list ℕ) def_local),

  trivial
end

end test_get

end def_local

-- Test: finally, make sure the `block_local` and `def_local` caches
-- don't collide.

namespace collision

open tactic.local_cache.cache_scope

def TEST_NS : name := `my_tactic

-- Example "expensive" function
meta def generate_some_data : tactic (list ℕ) :=
do trace_cache_regenerating,
   return [1, 2, 3, 4]

meta def tac_block : tactic unit :=
do my_cached_data ← run_once TEST_NS generate_some_data block_local,
   skip

meta def tac_def : tactic unit :=
do my_cached_data ← run_once TEST_NS generate_some_data def_local,
   skip

meta def fail_if_cache_miss_def : tactic unit :=
do p ← local_cache.present TEST_NS def_local,
   if p then skip else fail "cache miss"

meta def fail_if_cache_miss_block : tactic unit :=
do p ← local_cache.present TEST_NS block_local,
   if p then skip else fail "cache miss"

lemma my_lemma_1 : true := begin
  tac_block,
  fail_if_cache_miss_block,
  success_if_fail { fail_if_cache_miss_def },

  trivial
end

lemma my_lemma_2 : true := begin
  tac_def,
  fail_if_cache_miss_def,
  success_if_fail { fail_if_cache_miss_block },

  trivial
end

lemma my_lemma_3 : true := begin
  tac_block,
  tac_def,

  local_cache.clear TEST_NS block_local,
  fail_if_cache_miss_def,
  success_if_fail { fail_if_cache_miss_block },

  trivial
end

lemma my_lemma_4 : true := begin
  tac_block,
  tac_def,

  local_cache.clear TEST_NS def_local,
  fail_if_cache_miss_block,
  success_if_fail { fail_if_cache_miss_def },

  trivial
end

end collision
