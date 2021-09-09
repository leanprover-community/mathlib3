DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

cd $DIR/../.docker/debian/lean && \
docker build -t leanprovercommunity/lean:debian -t leanprovercommunity/lean:latest . && \
cd $DIR/../.docker/debian/mathlib && \
docker build -t leanprovercommunity/mathlib:debian -t leanprovercommunity/mathlib:latest .
cd $DIR/../.docker/gitpod/mathlib && \
docker build -t leanprovercommunity/mathlib:gitpod .
