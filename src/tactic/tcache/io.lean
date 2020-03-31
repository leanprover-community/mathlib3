import system.io

open io io.proc

namespace tcache

def CACHE_DIR := ".cache"

def exec_cmd (args : io.process.spawn_args) : io unit :=
spawn args >> return ()

def mk_cache_dir : io unit :=
  exec_cmd {cmd := "mkdir", args := ["-p", CACHE_DIR], stdout := io.process.stdio.null, stderr := io.process.stdio.null}

def rm_cache_dir : io unit :=
  exec_cmd {cmd := "rm", args := ["-rf", CACHE_DIR], stdout := io.process.stdio.null, stderr := io.process.stdio.null}

meta def read_to_end' (h : handle) : io string := do
cb ← (iterate none $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h $ 20000 * 1024,
      return $ some $ match r with
      | none := some c
      | some r := some (r ++ c)
      end
),
return $ match cb with
| none := ""
| some cb := cb.to_string
end

meta def file_read (fn : string) : io string := do
  h ← io.mk_file_handle fn io.mode.read ff,
  s ← read_to_end' h,
  return s

def file_write (fn : string) (data : string) : io unit := do
  h ← io.mk_file_handle fn io.mode.write ff,
  io.fs.write h data.to_char_buffer,
  io.fs.close h

end tcache
