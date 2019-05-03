#! /bin/bash

wget -O code.deb https://go.microsoft.com/fwlink/?LinkID=760868
sudo apt install -y git curl python3 python3-pip ./code.deb
rm code.deb
code --install-extension jroesch.lean
wget https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
wget https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/remote-install-update-mathlib.sh
bash remote-install-update-mathlib.sh
rm remote-install-update-mathlib.sh
