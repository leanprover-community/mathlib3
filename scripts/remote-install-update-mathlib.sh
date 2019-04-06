#! /bin/sh
USER="--user"
USER_MSG="(at user level)"
if [ "$1" = "--global" ]; then
    USER=""
    USER_MSG="(globally)"
fi
echo "Installing python dependencies $USER_MSG"
pip3 install $USER toml PyGithub urllib3 certifi GitPython || exit -1
echo "Fetching the update-mathlib script"
curl -o update-mathlib.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/update-mathlib.py
curl -o delayed_interrupt.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/delayed_interrupt.py
curl -o auth_github.py https://raw.githubusercontent.com/leanprover-community/mathlib/master/scripts/auth_github.py
echo "installing it in \$HOME/.mathlib/bin"
chmod +x update-mathlib.py
mkdir -p $HOME/.mathlib/bin || true
mv update-mathlib.py $HOME/.mathlib/bin/update-mathlib
mv delayed_interrupt.py $HOME/.mathlib/bin/
mv auth_github.py $HOME/.mathlib/bin/
if grep -q ".mathlib/bin" $HOME/.profile
then
    echo mathlib scripts are already added to \$PATH in .profile
else
    echo "Adding a path modification in .profile"
    touch $HOME/.profile
    echo "export PATH=\"\$HOME/.mathlib/bin:\$PATH\" " >> $HOME/.profile
    echo $HOME/.profile
    ls $HOME/.profile
    echo "You should now run \"source $HOME/.profile\""
fi
