DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

cd $DIR/../.docker/debian/lean && \
docker build -t leanprover/lean:debian -t leanprover/lean:latest . && \
cd $DIR/../.docker/alpine/lean && \
docker build -t leanprover/lean:alpine . && \
cd $DIR/../.docker/debian/mathlib && \
docker build -t leanprover/mathlib:debian -t leanprover/mathlib:latest .
cd $DIR/../.docker/alpine/mathlib && \
docker build -t leanprover/mathlib:alpine .
cd $DIR/../.docker/gitpod/mathlib && \
docker build -t leanprover/mathlib:gitpod .
