
import toml
import os.path
import os

# find root of project and leanpkg.toml
cwd = os.getcwd()
while not os.path.isfile('leanpkg.toml') and not os.getcwd() == '/':
    os.chdir(os.path.dirname(os.getcwd()))
if not os.path.isfile('leanpkg.toml'):
    raise('no leanpkg.toml found')

leanpkg = toml.load('leanpkg.toml')
version = leanpkg['package']['lean_version']
print('lean-' + version)
