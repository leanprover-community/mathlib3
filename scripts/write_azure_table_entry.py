import requests
import sys

file_hash = sys.argv[1]
git_hash = sys.argv[2]
token = sys.argv[3]

def get_url():
  return "https://oleanstorage.table.core.windows.net/oleanlookup?{0}".format(token)

def add_entry(file_hash, git_hash):
  r = requests.post(
    url = get_url(),
    json={'PartitionKey':'0', 'RowKey':file_hash, 'git':git_hash},
    headers={'Accept':'application/json;odata=nometadata'}
  )
  print(r.json())

add_entry(file_hash, git_hash)
