import os
import shutil

with open('bin/.vale_version') as f:
    version = f.read().splitlines()[0]
release = f'vale-release-{version}'
print(release)
shutil.copytree('bin', f'releases/{release}/{release}/bin', ignore = shutil.ignore_patterns('z3.exe'))
shutil.make_archive(f'releases/{release}', 'zip', f'releases/{release}')
