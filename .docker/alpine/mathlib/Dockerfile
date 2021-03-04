# This is the Dockerfile for `leanprovercommunity/mathlib:alpine`.
# It is based on the `leanprovercommunity/lean:alpine` image,
# and contains a cloned copy of the `mathlib` github repository,
# along with precompiled oleans.

FROM leanprovercommunity/lean:alpine

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true
# clone a copy of mathlib, and download precompiled oleans
RUN leanproject get mathlib
