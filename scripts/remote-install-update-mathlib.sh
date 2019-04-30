#! /bin/sh
BRANCH=master
USER="--user"
USER_MSG="(at user level)"
PYTHON_DEPS="setuptools toml PyGithub urllib3 certifi gitpython"

for i in "$@"
do
case $i in
    -b=*|--branch=*)
        BRANCH="${i#*=}"
    ;;
    --global)
        USER=""
        USER_MSG="(globally)"
    ;;
    *)
        echo unknown option "${i#*=}"
        echo "usage: remote-install-update-mathlib.sh [-b=BRANCH|--branch=BRANCH] [--global]"
        exit -1
    ;;
esac
done

echo "Installing python dependencies $USER_MSG"
if ! which pip3; then
    if which apt-get; then
        read -p "update-mathlib needs to install python3 and pip3. Proceed?" -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            sudo apt-get install python3 python3-pip
        else
            exit -1
        fi
    elif which brew; then
        read -p "update-mathlib needs to install python3 and pip3. Proceed?" -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            brew install python3
        else
            exit -1
        fi
    elif which choco; then
        read -p "update-mathlib needs to install python3 and pip3. Proceed?" -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            choco install python
        else
            exit -1
        fi
    else
        echo "python3 and pip3 not found. First install python3 and pip3 and then install update-mathlib"
        exit -1
    fi
fi

pip3 install --upgrade $USER $PYTHON_DEPS || exit -1
echo "Fetching the update-mathlib script"
curl -o update-mathlib.py https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/update-mathlib.py
curl -o cache-olean.py https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/cache-olean.py
curl -o setup-lean-git-hooks.sh https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/setup-lean-git-hooks.sh
curl -o delayed_interrupt.py https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/delayed_interrupt.py
curl -o auth_github.py https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/auth_github.py
curl -o post-commit https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/post-commit
curl -o post-checkout https://raw.githubusercontent.com/leanprover-community/mathlib/$BRANCH/scripts/post-checkout
echo "installing it in \$HOME/.mathlib/bin"
chmod +x update-mathlib.py
mkdir -p $HOME/.mathlib/bin || true
mkdir -p $HOME/.mathlib/hooks || true

mv update-mathlib.py       $HOME/.mathlib/bin/update-mathlib
mv cache-olean.py          $HOME/.mathlib/bin/cache-olean
mv delayed_interrupt.py    $HOME/.mathlib/bin/
mv auth_github.py          $HOME/.mathlib/bin/
mv setup-lean-git-hooks.sh $HOME/.mathlib/bin/setup-lean-git-hooks
mv post-commit   $HOME/.mathlib/hooks/
mv post-checkout $HOME/.mathlib/hooks/

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
