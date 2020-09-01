import meta.stacks
import all

/-!

Usage:

```bash
bash scripts/mk_all.sh
lean --run scripts/stacks_tags.lean
```

-/

open stacks tactic

meta def format_entry (decl_name : name) (tag : stacks_tag) : string :=
let comment := match tag.comment with
| some c := format!"\n  comment: \"{c}\""
| none := ""
end in
to_string $ format!
"\n\n{decl_name}:
  tag: \"{tag.tag}\"" ++ comment

meta def make_stacks_yaml : tactic string :=
do dcls ← attribute.get_instances `stacks,
   entries ← dcls.mmap (λ nm, format_entry nm <$> stacks_attribute.get_param nm),
   return $ string.join entries

open io io.fs
/--
Writes a file with the given contents.
-/
meta def io.write_file (fn : string) (contents : string) : io unit := do
h ← mk_file_handle fn mode.write,
put_str h contents,
close h

meta def main : io unit :=
do text ← run_tactic make_stacks_yaml,
   io.write_file "stacks.yaml" text
