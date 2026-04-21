#!/usr/bin/env bash
# Start the KIP Agent Dashboard
#
# Usage:
#   ./ui/start.sh              # default port 8081
#   ./ui/start.sh --port 3000  # custom port
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SERVER_DIR="$SCRIPT_DIR/server"
CLIENT_DIR="$SCRIPT_DIR/client"
PORT=8081

while [[ $# -gt 0 ]]; do
    case "$1" in
        --port) PORT="$2"; shift 2 ;;
        *)      break ;;
    esac
done

# Install server deps if needed
if [[ ! -d "$SERVER_DIR/node_modules" ]]; then
    echo "Installing server dependencies..."
    cd "$SERVER_DIR" && npm install
fi

# Install client deps and build if needed
if [[ ! -d "$CLIENT_DIR/dist" ]]; then
    if [[ ! -d "$CLIENT_DIR/node_modules" ]]; then
        echo "Installing client dependencies..."
        cd "$CLIENT_DIR" && npm install
    fi
    echo "Building client..."
    cd "$CLIENT_DIR" && npm run build
fi

echo "Starting KIP Dashboard on port $PORT..."
cd "$SERVER_DIR" && npx tsx src/index.ts --project "$PROJECT_ROOT" --port "$PORT"
