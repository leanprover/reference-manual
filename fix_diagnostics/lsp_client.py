"""LSP client with manual JSON-RPC over stdio (no dependencies)."""

import json
import subprocess
import threading
import queue
import time
from pathlib import Path
from typing import Dict, List, Optional, Any


class LspClient:
    """
    Manual LSP client using JSON-RPC over stdio.
    No external dependencies.

    Features:
    - Manages Lean RPC sessions with automatic keepalive messages
    - Caches RPC sessions per file URI for efficiency
    - Sends keepalive every 2.5 seconds during long operations to prevent timeout
    - Tracks opened files to avoid reopening them (important for persistent clients)
    """

    def __init__(self, server_cmd: Optional[List[str]] = None) -> None:
        """
        Initialize LSP client.

        Args:
            server_cmd: Command to start LSP server (default: ['lake', 'serve'])
        """
        if server_cmd is None:
            server_cmd = ["lake", "serve"]

        self.process = subprocess.Popen(
            server_cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,  # Unbuffered
        )
        self.msg_id = 0
        self.pending_requests: Dict[int, "queue.Queue[Dict[str, Any]]"] = {}  # msg_id → response queue
        self.diagnostics_by_uri: Dict[str, List[Dict[str, Any]]] = {}  # uri → list of diagnostics
        self.file_progress: Dict[str, bool] = {}  # uri → processing status (True/False)
        self.shutdown_flag = False
        self.initialized = False

        # RPC session management
        self.rpc_sessions: Dict[str, str] = {}  # uri → session_id
        self.rpc_session_lock = threading.Lock()

        # Track opened files to avoid reopening them
        self.opened_files: set[str] = set()  # set of URIs

        # Background thread reads responses/notifications
        self.reader_thread = threading.Thread(target=self._read_loop, daemon=True)
        self.reader_thread.start()

    def _read_loop(self) -> None:
        """Background thread to read LSP messages."""
        assert self.process.stdout is not None
        while not self.shutdown_flag:
            try:
                # Read Content-Length header
                header_line = self.process.stdout.readline()
                if not header_line:
                    break

                header = header_line.decode("utf-8").strip()
                if not header.startswith("Content-Length:"):
                    continue

                content_length = int(header.split(":")[1].strip())

                # Skip any additional headers until we hit the blank line
                while True:
                    line = self.process.stdout.readline()
                    if line.strip() == b"":
                        break

                # Read JSON body
                body = self.process.stdout.read(content_length)
                if not body:
                    break

                message = json.loads(body.decode("utf-8"))

                # Handle message
                if "id" in message and ("result" in message or "error" in message):
                    # Response to our request
                    msg_id = message["id"]
                    if msg_id in self.pending_requests:
                        self.pending_requests[msg_id].put(message)
                elif "method" in message:
                    # Notification from server
                    self._handle_notification(message)

            except Exception as e:
                if not self.shutdown_flag:
                    print(f"Error reading LSP message: {e}")
                break

    def _handle_notification(self, message: Dict[str, Any]) -> None:
        """Handle server notifications."""
        method = message.get("method")
        params = message.get("params", {})

        if method == "textDocument/publishDiagnostics":
            uri = params.get("uri")
            diagnostics = params.get("diagnostics", [])
            self.diagnostics_by_uri[uri] = diagnostics
        elif method == "$/lean/fileProgress":
            # Track file processing progress
            # Lean's format: {textDocument: {uri, version}, processing: [{kind, range}, ...]}
            # File is done when processing array is empty
            text_document = params.get("textDocument", {})
            uri = text_document.get("uri")
            processing_items = params.get("processing", [])

            if uri:
                # True if there are items being processed, False if empty (done)
                self.file_progress[uri] = len(processing_items) > 0

    def _send_message(self, msg: Dict[str, Any]) -> None:
        """Send JSON-RPC message with Content-Length header."""
        assert self.process.stdin is not None
        body = json.dumps(msg).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("utf-8")
        self.process.stdin.write(header + body)
        self.process.stdin.flush()

    def send_request(self, method: str, params: Dict[str, Any], timeout: int = 30) -> Any:
        """Send request and wait for response."""
        self.msg_id += 1
        msg_id = self.msg_id
        response_queue: "queue.Queue[Dict[str, Any]]" = queue.Queue()
        self.pending_requests[msg_id] = response_queue

        self._send_message(
            {"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params}
        )

        # Wait for response
        try:
            response = response_queue.get(timeout=timeout)
            del self.pending_requests[msg_id]

            if "error" in response:
                raise Exception(f"LSP error: {response['error']}")

            return response.get("result")
        except queue.Empty:
            if msg_id in self.pending_requests:
                del self.pending_requests[msg_id]
            raise TimeoutError(f"LSP request timeout: {method}")

    def send_notification(self, method: str, params: Dict[str, Any]) -> None:
        """Send notification (no response expected)."""
        self._send_message({"jsonrpc": "2.0", "method": method, "params": params})

    def initialize(self, root_path: Optional[Path] = None) -> Any:
        """Initialize LSP server."""
        if self.initialized:
            return

        if root_path is None:
            root_path = Path.cwd()

        root_uri = root_path.absolute().as_uri()

        result = self.send_request(
            "initialize",
            {
                "processId": None,
                "rootUri": root_uri,
                "capabilities": {
                    "textDocument": {
                        "codeAction": {
                            "codeActionLiteralSupport": {
                                "codeActionKind": {
                                    "valueSet": ["quickfix", "refactor", "source"]
                                }
                            }
                        }
                    }
                },
                "initializationOptions": {
                    "hasWidgets": True
                },
            },
        )

        self.send_notification("initialized", {})
        self.initialized = True
        return result

    def did_open(self, file_path: Path, text: str) -> bool:
        """
        Open file in LSP (non-blocking).

        Sends textDocument/didOpen notification and returns immediately.
        The Lean server will process the file asynchronously.

        If the file is already open, this is a no-op.

        Args:
            file_path: Path to file
            text: File content

        Returns:
            bool: True if file was opened, False if already open
        """
        file_uri = Path(file_path).absolute().as_uri()

        # Skip if already open
        if file_uri in self.opened_files:
            return False

        self.send_notification(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": file_uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": text,
                }
            },
        )

        # Mark as opened
        self.opened_files.add(file_uri)
        return True

    def get_diagnostics(self, file_path: Path) -> List[Dict[str, Any]]:
        """
        Get diagnostics for a file (blocks until processing complete).

        Waits for the Lean server to finish processing the file using
        $/lean/fileProgress notifications, then returns diagnostics from
        publishDiagnostics notifications.

        Args:
            file_path: Path to file

        Returns:
            List of LSP diagnostics
        """
        file_uri = Path(file_path).absolute().as_uri()

        # Wait for file processing to complete
        # Use Lean's $/lean/fileProgress notifications
        timeout = 60  # seconds
        poll_interval = 0.1
        elapsed = 0.0
        last_keepalive = 0.0
        keepalive_interval = 2.5  # Send keepalive every 2.5 seconds

        while elapsed < timeout:
            # Check if file is done processing
            is_processing = self.file_progress.get(file_uri, None)

            if is_processing is False:
                # File processing complete (progress notification with empty array)
                break
            elif is_processing is None:
                # No progress notification yet - check if we have diagnostics
                # This handles cached/fast files
                if file_uri in self.diagnostics_by_uri:
                    # Got diagnostics without progress notification, assume done
                    break

            # Send keepalive for RPC sessions periodically to prevent timeout
            if elapsed - last_keepalive >= keepalive_interval:
                self.rpc_keepalive_all()
                last_keepalive = elapsed

            time.sleep(poll_interval)
            elapsed += poll_interval

        return self.diagnostics_by_uri.get(file_uri, [])

    def code_action(
        self, file_path: Path, line: int, col: int, diagnostics: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Request code actions at a position.

        Args:
            file_path: Path to file
            line: Line number (0-based)
            col: Column number (0-based)
            diagnostics: List of LSP diagnostics

        Returns:
            List of code actions
        """
        file_uri = Path(file_path).absolute().as_uri()

        result = self.send_request(
            "textDocument/codeAction",
            {
                "textDocument": {"uri": file_uri},
                "range": {
                    "start": {"line": line, "character": col},
                    "end": {"line": line, "character": col},
                },
                "context": {"diagnostics": diagnostics},
            },
        )

        return result or []

    def apply_workspace_edit(self, edit: Dict[str, Any]) -> Any:
        """
        Apply workspace edit.

        Args:
            edit: LSP WorkspaceEdit

        Returns:
            Apply edit result
        """
        result = self.send_request("workspace/applyEdit", {"edit": edit})
        return result

    def rpc_connect(self, file_path: Path) -> str:
        """
        Connect to Lean RPC for a file (or reuse existing session).

        Args:
            file_path: Path to file

        Returns:
            Session ID for RPC calls
        """
        file_uri = Path(file_path).absolute().as_uri()

        # Check if we already have a session for this file
        with self.rpc_session_lock:
            if file_uri in self.rpc_sessions:
                return self.rpc_sessions[file_uri]

            # Create new session
            result = self.send_request("$/lean/rpc/connect", {"uri": file_uri})
            session_id = result["sessionId"]
            self.rpc_sessions[file_uri] = session_id
            return session_id

    def rpc_keepalive(self, session_id: str) -> None:
        """
        Send keepalive for RPC session.

        Args:
            session_id: RPC session ID to keep alive
        """
        # Send a keepalive request to prevent session timeout
        # Lean RPC keepalive is done via $/lean/rpc/keepAlive
        try:
            self.send_request("$/lean/rpc/keepAlive", {"sessionId": session_id}, timeout=5)
        except Exception:
            # Keepalive failures are not critical - session might already be alive
            pass

    def rpc_keepalive_all(self) -> None:
        """Send keepalive for all active RPC sessions."""
        with self.rpc_session_lock:
            for session_id in self.rpc_sessions.values():
                self.rpc_keepalive(session_id)

    def rpc_call(
        self,
        session_id: str,
        file_path: Path,
        method: str,
        params: Dict[str, Any],
    ) -> Any:
        """
        Call Lean RPC method.

        Args:
            session_id: RPC session ID from rpc_connect
            file_path: Path to file
            method: RPC method name
            params: Method parameters

        Returns:
            RPC method result
        """
        file_uri = Path(file_path).absolute().as_uri()
        result = self.send_request(
            "$/lean/rpc/call",
            {
                "sessionId": session_id,
                "method": method,
                "params": params,
                "textDocument": {"uri": file_uri},
                "position": {"line": 0, "character": 0},
            },
        )
        return result

    def get_interactive_diagnostics(self, file_path: Path) -> List[Dict[str, Any]]:
        """
        Get interactive diagnostics with widget data for a file.

        Args:
            file_path: Path to file

        Returns:
            List of interactive diagnostics with widget components
        """
        file_uri = Path(file_path).absolute().as_uri()

        # Try with cached session first
        session_id = self.rpc_connect(file_path)
        try:
            return self.rpc_call(
                session_id,
                file_path,
                "Lean.Widget.getInteractiveDiagnostics",
                {"lineRange?": None},
            )
        except Exception as e:
            # If session is outdated, clear cache and retry with fresh session
            error_str = str(e)
            if "Outdated RPC session" in error_str or "-32900" in error_str:
                with self.rpc_session_lock:
                    if file_uri in self.rpc_sessions:
                        del self.rpc_sessions[file_uri]

                # Retry with fresh session
                session_id = self.rpc_connect(file_path)
                return self.rpc_call(
                    session_id,
                    file_path,
                    "Lean.Widget.getInteractiveDiagnostics",
                    {"lineRange?": None},
                )
            else:
                # Re-raise if it's a different error
                raise

    def shutdown(self) -> None:
        """Shutdown LSP server."""
        if self.shutdown_flag:
            return

        self.shutdown_flag = True
        try:
            if self.initialized:
                self.send_request("shutdown", {}, timeout=5)
                self.send_notification("exit", {})
            self.process.wait(timeout=5)
        except Exception:
            self.process.kill()
            self.process.wait()

    def __enter__(self) -> "LspClient":
        self.initialize()
        return self

    def __exit__(self, *args: Any) -> None:
        self.shutdown()
