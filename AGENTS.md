# PROJECT KNOWLEDGE BASE

**Generated:** 2026-02-01
**GitHub:** FrankieeW/GroupAction-Lean
**Author:** Frankie F.-C. Wang

## OVERVIEW

Lean 4 formalization of the GroupAction mathematical project. Contains mathematical proofs, definitions, and formal verification using the Lean 4 theorem prover.

Mathlib-style library defining `GroupAction` class and core results: permutation representation, stabilizer subgroup, and examples (S₃, D₄, etc.).

## STRUCTURE

```
Lean/
├── GroupAction/              # Main library (GroupAction namespace)
│   ├── GroupAction.lean      # Main entry, imports all, #lint
│   ├── Defs.lean             # GroupAction class, faithful, transitive
│   ├── Basic.lean            # Iff.rfl theorems for definitions
│   ├── Permutation.lean      # sigma, sigmaPerm, phi, phi_apply, phi_mul
│   ├── Stabilizer.lean       # stabilizerSet, stabilizer (Subgroup G)
│   └── Examples.lean         # Instances: S₃, D₄, group/subgroup actions
├── *.lean                    # Root-level files (rare)
├── Lake.toml                 # Lean project configuration
├── lake-manifest.json        # Dependency lock
└── lean-toolchain            # Lean version specification
```

## WHERE TO LOOK

| Concept | File | Key Definitions |
|---------|------|-----------------|
| Action axioms | `Defs.lean` | `act`, `ga_mul`, `ga_one` |
| Faithful/transitive | `Defs.lean` | `GroupAction.faithful`, `GroupAction.transitive` |
| Permutation rep | `Permutation.lean` | `sigma`, `sigmaPerm`, `phi`, `phi_apply`, `phi_mul` |
| Stabilizer | `Stabilizer.lean` | `stabilizerSet`, `stabilizer` |
| S₃ example | `Examples.lean` | `s3ActionFin3`, `s3Action_transitive` |
| D₄ example | `Examples.lean` | `d4ActionZMod4`, `d4CenterAction` |

---

## COMMANDS

```bash
# Build project (all targets)
lake build

# Build specific target
lake build GroupAction

# Run all tests
lake test

# Run single test file (use Lean's --run)
lake exe lean --run GroupAction/TestFile.lean

# Run tests via Lake's test runner
lake test --filter "test_name"

# Lint current file (auto-check in VS Code)
# Add #lint at end of file for manual lint check

# Check imports
lean --deps

# Format file
lean --run Formatter.lean

# Check for unused variables
lean --run Lean.FileParser

# Open Lean REPL
lake repl
```

---

## CODE STYLE GUIDELINES

### File Structure & Headers

Every `.lean` file MUST have a header:

```lean
/-
Title: FileName.lean
Project: Project Name
Author: Frankie Feng-Cheng WANG
Date: June 2026
Copyright (c) 2026 Frankie Feng-Cheng WANG. All rights reserved.
Repository: https://github.com/FrankieeW/GroupAction
-/
```

### Imports

- **Group by category**: Mathlib imports first, then local imports
- **Alphabetical within groups**
- **One import per line**
- **Use relative imports** with `GroupAction.X` prefix for local modules

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Perm.Basic
import GroupAction.Defs
```

### Documentation Comments

- **Section headers**: `/-! ## Section Name -/`
- **Definitions**: `/-- Description. -/`
- **Multi-line**: Stack `/--` on separate lines

```lean
/-! ## Definitions: group actions -/

/-- A group action of a monoid `G` on type `X`. -/
def myDef := ...

/-- Detailed description.
  Multi-line documentation here. -/
def myOtherDef := ...
```

### Naming Conventions

- **Files**: `snake_case` (e.g., `group_action_definitions.lean`)
- **Definitions/Theorems**: `camelCase` (Lean convention)
- **Constants**: `snake_case`
- **Types/Classes**: `PascalCase`

### Proof Style

- Use `by` tactic mode for proofs
- Prefer `rw`, `simp`, `intro`, `cases` over explicit term construction
- Use `calc` chains for multi-step proofs with step-by-step comments
- Chain tactics on same line when natural

```lean
theorem myTheorem (h : P) : Q := by
  rw [h]
  simp
```

### Local Variables

Use `variable` for section-level implicit parameters:

```lean
variable {G : Type*} [Group G] {X : Type*} [GroupAction G X]
```

### File Termination

Always end files with `#lint` for automatic style checking.

---

## ANTI-PATTERNS

- **NEVER skip `#lint`** at file end
- **NEVER use `sorry`** in proofs
- **NEVER rely on implicit arguments** — must explicitly declare `[Group G]`, `[GroupAction G X]`
- **Hardcoding numbers** → Use named constants
- **Manual rewrites without lemmas** → Use `simp`/`rw` lemmas
- **Missing imports** → Run `lake build` to verify
- **Missing doc comments** → Document all public definitions

---

## MATHLIB CONVENTIONS

Follow the [mathlib style guide](https://github.com/leanprover-community/mathlib4/wiki/mathlib-style):

- Use `·` (centered dot) for function arguments: `f x · y`
- Prefer `haveI` / `letI` over explicit instance arguments
- Use `obtain` for destructuring `∃` / `∧`
- Use `rcases` for complex pattern matching

**Project settings:** `autoImplicit = false`, two-space indent

---

## GITIGNORE

```
# Lean build artifacts
build/
lake-packages/
*.olean
*.olean.lock

# Editor
.vscode/
.DS_Store

# Environment
.env
*.log

# Dependencies
Mathlib/  # Use mathlib as dependency, don't commit
```

---

## NOTES

- Coordinate with Orch-GroupAction for CI/release
- All code must pass `lake build` before submission
