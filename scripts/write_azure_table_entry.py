import requests
import sys

file_hash = sys.argv[1]
git_hash = sys.argv[2]
token = sys.argv[3]

lookup_url = 'https://oleanstorage.table.core.windows.net/oleanlookup?' + token

def add_entry(file_hash, git_hash):
  r = requests.post(
    url = lookup_url,
    json={'PartitionKey':'0', 'RowKey':file_hash, 'git':git_hash},
    headers={'Accept':'application/json;odata=nometadata'}
  )
  print(r.json())

add_entry(file_hash, git_hash)
