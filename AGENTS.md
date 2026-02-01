# PROJECT KNOWLEDGE BASE

**Generated:** 2026-02-01
**GitHub:** FrankieeW/GroupAction-Lean
**Author:** Frankie F.-C. Wang

## OVERVIEW

Lean 4 formalization of the GroupAction mathematical project. Contains mathematical proofs, definitions, and formal verification using the Lean 4 theorem prover.

## STRUCTURE

```
Lean/
├── *.lean              # Mathlib-style formalization files
├── Mathlib/            # (ignored) Local mathlib copy
└── Lake.toml           # Lean project configuration
```

## WHERE TO LOOK

| Task | Location | Notes |
|------|----------|-------|
| Formal proofs | `*.lean` files | Follow mathlib conventions |
| Project config | `Lake.toml` | Lean 4 lake build system |
| Dependencies | `lean-toolchain` | Specify Lean version |

## CONVENTIONS

- **File naming**: snake_case, descriptive (e.g., `group_action_definitions.lean`)
- **Style**: Follow [mathlib style guide](https://github.com/leanprover-community/mathlib4/wiki/mathlib-style)
- **Proofs**: Use `by` and `rw` idioms
- **Imports**: Group by category, alphabetical within

## ANTI-PATTERNS (THIS PROJECT)

- **Hardcoding numbers** → Use named constants
- **Manual rewrites** → Use `simp`/`rw` lemmas
- **Missing imports** → Run `lean --make` to verify

## COMMANDS

```bash
# Build project
lake build

# Run tests
lake test

# Format code
lean --run Formatter.lean

# Check imports
lean --deps
```

## NOTES

- Greenfield: No formalization yet
- Coordinate with Orch-GroupAction for CI/release
