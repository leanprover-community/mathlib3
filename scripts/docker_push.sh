# This script attempts to build all the docker images, and then push then to the repository.
# You'll need to have run `docker login` already;
# check with scott.morrison@gmail.com for credentials.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

cd $DIR
./docker_build.sh
docker push leanprover/lean:latest
docker push leanprover/lean:debian
docker push leanprover/lean:alpine
docker push leanprover/mathlib:latest
docker push leanprover/mathlib:debian
docker push leanprover/mathlib:alpine
docker push leanprover/mathlib:gitpod
