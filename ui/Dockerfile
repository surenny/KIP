# Stage 1: Build client
FROM node:22-slim AS client-builder
WORKDIR /build
COPY ui/client/package*.json ./
RUN npm ci
COPY ui/client/ ./
RUN npm run build

# Stage 2: Build server
FROM node:22-slim AS server-builder
WORKDIR /build
COPY ui/server/package*.json ./
RUN npm ci
COPY ui/server/ ./
RUN npm run build

# Stage 3: Runtime
FROM node:22-slim
RUN apt-get update && apt-get install -y --no-install-recommends \
    graphviz \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Production server deps (includes native better-sqlite3, compiled for this image)
COPY ui/server/package*.json ./server/
RUN cd server && npm ci --omit=dev

# Compiled server JS
COPY --from=server-builder /build/dist ./server/dist

# Built client — must be at /app/client/dist so that
# server/dist/index.js's `../../client/dist` resolves correctly
COPY --from=client-builder /build/dist ./client/dist

EXPOSE 8081

CMD ["node", "server/dist/index.js", "--project", "/project", "--port", "8081"]
