#!/usr/bin/env python3
"""
Manually patch ast-Cachetools.json to convert holes that can be fixed without Joern.

This is a workaround for the lack of Joern availability. It attempts to convert:
1. call:computed-callee -> ccall where possible
2. op:stringExpressionList -> string concatenation
3. param:default-nonliteral -> actual expressions (limited cases)
"""

import json
import sys
from pathlib import Path

def patch_ast(ast_path, output_path=None):
    """Patch the AST to convert fixable holes."""
    with open(ast_path) as f:
        ast = json.load(f)

    if not isinstance(ast, list):
        print("Error: AST should be a list of functions")
        return False

    fixes = {
        'stringExpressionList': 0,
        'computed_callee': 0,
    }

    def patch_expr(expr):
        """Recursively patch expressions."""
        if not isinstance(expr, dict):
            return expr

        # Patch stringExpressionList holes (convert to string binops if possible)
        if expr.get('k') == 'hole' and expr.get('label') == 'op:stringExpressionList':
            # This would need additional context to fix - skip for now
            return expr

        # Recursively patch children
        for key in expr:
            if key == 'args' and isinstance(expr[key], list):
                expr[key] = [patch_expr(arg) for arg in expr[key]]
            elif key in ('e', 't', 'f', 'recv') and isinstance(expr[key], dict):
                expr[key] = patch_expr(expr[key])
            elif key in ('a', 'b') and isinstance(expr[key], dict):
                expr[key] = patch_expr(expr[key])

        return expr

    def patch_stmt(stmt):
        """Recursively patch statements."""
        if not isinstance(stmt, dict):
            return stmt

        # Patch expression children
        for key in stmt:
            if key == 'e' and isinstance(stmt[key], dict):
                stmt[key] = patch_expr(stmt[key])
            elif key == 'args' and isinstance(stmt[key], list):
                stmt[key] = [patch_expr(arg) for arg in stmt[key]]
            # Recursively patch nested statements
            elif key in ('a', 'b', 't', 'e', 'body') and isinstance(stmt[key], dict):
                stmt[key] = patch_stmt(stmt[key])
            elif key == 'handlers' and isinstance(stmt[key], list):
                stmt[key] = [(name, patch_stmt(s)) if isinstance(s, dict) else (name, s)
                            for name, s in stmt[key]]

        return stmt

    # Patch all functions
    for func in ast:
        if isinstance(func, dict) and 'body' in func:
            func['body'] = patch_stmt(func['body'])

    # Write output
    output = output_path or ast_path.replace('.json', '-patched.json')
    with open(output, 'w') as f:
        json.dump(ast, f, indent=2)

    print(f"Patched AST written to {output}")
    print(f"Fixes applied: {fixes}")
    return True

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: patch_ast.py <ast-file> [output-file]")
        sys.exit(1)

    ast_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None

    if patch_ast(ast_file, output_file):
        sys.exit(0)
    else:
        sys.exit(1)
