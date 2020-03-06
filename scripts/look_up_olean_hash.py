import sys
import requests

read_access_token = 'sv=2019-02-02&ss=t&srt=sco&sp=r&se=2023-11-01T18:45:01Z&st=2020-03-04T10:45:01Z&spr=https&sig=veKTtXzeziJU%2B1%2FCxNGhr3wziRE2QrMJGk%2BzzYQK%2Fu4%3D'

file_hash = sys.argv[1]

def get_url():
  return "https://oleanstorage.table.core.windows.net/oleanlookup(PartitionKey='0',RowKey='{0}')?$select=git&{1}".format(
    file_hash, read_access_token
  )

r = requests.get((get_url()), headers={'Accept':'application/json;odata=nometadata'}).json()

if 'git' in r:
  print(r['git'])
else:
  exit(1)
