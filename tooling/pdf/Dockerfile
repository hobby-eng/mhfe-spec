FROM node:26.10.0-bookworm-slim@sha256:3ffc19ea878019d9e9ae8971732ad4a03cda44f167107173174b60ed7c65bed3

ENV PLAYWRIGHT_BROWSERS_PATH=/ms-playwright \
    MHFE_PDF_DEPENDENCIES=/opt/pdf-toolchain \
    TZ=UTC \
    LANG=C.UTF-8
WORKDIR /opt/pdf-toolchain
COPY package.json pnpm-lock.yaml pnpm-workspace.yaml ./
RUN npm install --global corepack@0.36.0 && corepack enable \
    && pnpm install --frozen-lockfile \
    && pnpm exec playwright install --with-deps chromium \
    && apt-get update && apt-get install -y --no-install-recommends git fonts-liberation \
    && rm -rf /var/lib/apt/lists/* \
    && chmod -R a+rX /opt/pdf-toolchain /ms-playwright
WORKDIR /work
