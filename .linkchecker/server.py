#!/usr/bin/env python3
"""
Simple HTTP server that adds a LinkChecker header to allow unlimited request rate.
"""
import http.server
import sys

class LinkCheckerHTTPRequestHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        # Add LinkChecker header to allow maxrequestspersecond > 10
        self.send_header('LinkChecker', 'allowed')
        super().end_headers()

if __name__ == '__main__':
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8877
    directory = sys.argv[2] if len(sys.argv) > 2 else '.'

    import os
    os.chdir(directory)

    with http.server.HTTPServer(('', port), LinkCheckerHTTPRequestHandler) as httpd:
        print(f"Serving at port {port} with LinkChecker header enabled")
        httpd.serve_forever()
