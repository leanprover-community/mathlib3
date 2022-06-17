from typing import Dict, Optional, Tuple, List
import yaml
import sys

def tiered_extract(db: Dict[str, Dict[str, Dict[str, Optional[str]]]]) -> List[Tuple[str, str]]:
  """From a three-level deep nested dictionary, return a list of (key, values)
  of the deepest level."""
  out = []
  for entry in db.values():
    for values in entry.values():
      for name, decl in values.items():
        if decl and '/' not in decl:
          out.append((name, decl))
  return out

def print_list(fn: str, pairs: List[Tuple[str, str]]) -> None:
  with open(fn, 'w') as out:
    for (id, val) in pairs:
      out.write(f'{id}\n{val.strip()}\n\n')

hundred_yaml = sys.argv[1]
overview_yaml = sys.argv[2]
undergrad_yaml = sys.argv[3]

with open(hundred_yaml, 'r') as hy:
  hundred = yaml.safe_load(hy)
with open(overview_yaml, 'r') as hy:
  overview = yaml.safe_load(hy)
with open(undergrad_yaml, 'r') as hy:
  undergrad = yaml.safe_load(hy)

hundred_decls:List[Tuple[str, str]] = []

for index, entry in hundred.items():
  if 'decl' in entry:
    hundred_decls.append((index, entry['decl']))
  elif 'decls' in entry:
    hundred_decls = hundred_decls + [(index, d) for d in entry['decls']]

overview_decls = tiered_extract(overview)
undergrad_decls = tiered_extract(undergrad)

print_list('100.txt', hundred_decls)
print_list('overview.txt', overview_decls)
print_list('undergrad.txt', undergrad_decls)
