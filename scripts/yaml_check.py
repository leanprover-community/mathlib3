import yaml
import sys

def tiered_extract(db):
  out = []
  for _, entry in db.items():
    for _, values in entry.items():
      for name, decl in values.items():
        if decl is not None and decl != '' and '/' not in decl:
          out.append((name, decl))
  return out

def print_list(fn, pairs):
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

hundred_decls = []
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
