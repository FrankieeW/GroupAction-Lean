# PROJECT KNOWLEDGE BASE

**Generated:** 2025-02-01
**Repository:** https://github.com/FrankieeW/GroupAction-Lean (GitHub)
**Repository:** https://codeberg.org/FrankieW/GroupAction-Lean (Codeberg)
**Author:** Frankie F.-C. Wang
**Lean Version:** 4.27.0
**Mathlib Version:** v4.27.0

---

## OVERVIEW

Lean 4 formalization of group actions using mathlib4 conventions. This project defines a custom `GroupAction` typeclass and proves fundamental results including:
- Permutation representation (φ: G → Equiv.Perm X)
- Stabilizer subgroups
- Examples: symmetric groups (S₃), dihedral groups (D₄)

**Style:** Mathlib-compatible library with full documentation, `#lint` checks, and formal proofs.

---

## PROJECT STRUCTURE

```
GroupAction-Lean/
├── GroupAction/              # Main library (GroupAction namespace)
│   ├── Defs.lean            # GroupAction class, faithful, transitive
│   ├── Basic.lean           # Iff.rfl theorems for definitions
│   ├── Permutation.lean     # sigma, sigmaPerm, phi, phi_apply, phi_mul
│   ├── Stabilizer.lean      # stabilizerSet, stabilizer (Subgroup G)
│   └── Examples.lean        # Instances: S₃, D₄, group/subgroup actions
├── GroupAction.lean         # Main entry point, imports all modules, #lint
├── lakefile.toml            # Lake build configuration
├── lake-manifest.json       # Dependency lock file (auto-generated)
├── lean-toolchain           # Lean version specification
├── doc/
│   ├── AGENTS.md            # (deprecated, use root AGENTS.md)
│   └── COMMIT_RULES.md      # Git commit message conventions
└── .lake/                   # Build artifacts (gitignored)
```

---

## BUILD & TEST COMMANDS

### Build Commands

```bash
# Build entire project
lake build

# Build specific module/target
lake build GroupAction
lake build GroupAction.Permutation

# Clean build artifacts
lake clean

# Update dependencies (mathlib)
lake update

# Check if build is up to date (no build)
lake check-build
```

### Testing & Verification

```bash
# Run all tests (if test suite exists)
lake test

# Verify single file compiles
lake env lean GroupAction/Defs.lean

# Run Lean file directly (for files with #eval or main)
lake exe lean --run GroupAction/Examples.lean

# Check file for errors without building
lean --check GroupAction/Defs.lean

# Interactive REPL
lake repl
```

### Linting

```bash
# Lint entire project
lake exe lint

# Check lint configuration
lake check-lint

# Lint specific file (add #lint at end of .lean file)
# Then build or open in VS Code with lean4 extension
```

### Single Test/Module Workflow

To work on a single file:
1. Open file in VS Code with lean4 extension
2. Edit code - errors show in real-time via LSP
3. Add `#lint` at file end to verify style
4. Run `lake build <filename>` to verify compilation
5. Check dependencies with `#check` or `#print`

---

## CODE STYLE GUIDELINES

### File Header (REQUIRED)

Every `.lean` file MUST start with:

```lean
/-
Title: FileName.lean
Project: Project 1 (Group Actions)
Author: Frankie Feng-Cheng WANG
Date: June 2026
Copyright (c) 2026 Frankie Feng-Cheng WANG. All rights reserved.
Repository:
  GitHub: https://github.com/FrankieeW/GroupAction-Lean
  Codeberg: https://codeberg.org/FrankieW/GroupAction-Lean
-/
```

### Import Organization

```lean
-- 1. Mathlib imports (alphabetical)
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Perm.Basic

-- 2. Local project imports (alphabetical, with GroupAction. prefix)
import GroupAction.Basic
import GroupAction.Defs
```

**Rules:**
- Group Mathlib imports first, then local imports
- Alphabetical order within each group
- One import per line
- Use `GroupAction.X` prefix for local modules

### Documentation Comments

```lean
/-! ## Section Title -/

/-- Single-line documentation for definitions/theorems. -/
def myFunction := ...

/-- Multi-line documentation.
    Indent continuation lines with 4 spaces.
    Use proper punctuation. -/
theorem myTheorem : P → Q := by
  sorry
```

**Patterns:**
- Section headers: `/-! ## Section Name -/`
- Definition docs: `/-- Description. -/` (before declaration)
- Inline comments: `-- Explanation` (within proofs)
- Block comments: `/-` ... `-/`

### Naming Conventions

| Type | Convention | Example |
|------|------------|---------|
| Files | `PascalCase.lean` | `Defs.lean`, `Permutation.lean` |
| Definitions | `camelCase` | `sigma`, `sigmaPerm`, `phi` |
| Theorems/Lemmas | `snake_case` | `phi_apply`, `phi_mul`, `group_action_to_perm_representation` |
| Classes/Types | `PascalCase` | `GroupAction`, `Equiv.Perm` |
| Constants | `camelCase` | `ga_mul`, `ga_one` |

### Type Classes & Variables

Use `variable` for section-wide implicit parameters:

```lean
variable {G : Type*} [Group G] {X : Type*} [GroupAction G X]

def sigma (g : G) : X → X :=
  fun x => GroupAction.act g x
```

**Instance Arguments:**
- Always explicit: `[Group G]`, `[GroupAction G X]`
- Use `haveI` / `letI` for temporary instances (mathlib convention)

### Proof Style

```lean
-- ✅ GOOD: Structured calc proof with comments
lemma phi_apply (g : G) (x : X) : phi g x = GroupAction.act g x := rfl

theorem phi_mul (g₁ g₂ : G) : phi (g₁ * g₂) = phi g₁ * phi g₂ := by
  apply Equiv.ext
  intro x
  calc
    phi (g₁ * g₂) x = GroupAction.act (g₁ * g₂) x := rfl
    _ = GroupAction.act g₁ (GroupAction.act g₂ x) := GroupAction.ga_mul g₁ g₂ x

-- ✅ GOOD: Simple tactic proof
lemma phi_one : phi (1 : G) = (1 : Equiv.Perm X) := by
  apply Equiv.ext
  intro x
  simp [phi, GroupAction.ga_one]
```

**Preferences:**
- Use `by` for tactic mode (default)
- Prefer `calc` for multi-step equational reasoning
- Use `rfl` for definitional equality
- Chain tactics with `;` when natural
- Use `simp`, `rw`, `intro`, `apply` over explicit terms

### Formatting

- **Indentation:** 2 spaces (configured in `lakefile.toml`)
- **Line length:** Max 100 chars (linter enforced)
- **Unicode:** Use `·` (centered dot) for placeholders: `f x · y`
- **Implicit args:** Explicit syntax when needed: `phi (X := X)`

### File Termination

**ALWAYS end files with:**

```lean
#lint
```

This runs automatic style checks (unused variables, naming conventions, etc.)

---

## MATHLIB CONVENTIONS

Follow [mathlib4 style guide](https://github.com/leanprover-community/mathlib4/wiki/mathlib-style):

- Use `·` (centered dot) for function argument placeholders
- Prefer `haveI` / `letI` over explicit instance arguments
- Use `obtain` for destructuring `∃` / `∧`
- Use `rcases` for complex pattern matching
- Prefer `simp` lemmas over manual rewrites
- Document all public definitions

**Project Settings (lakefile.toml):**
```toml
pp.unicode.fun = true          # Pretty-print unicode
autoImplicit = false           # Disable auto-implicit arguments
relaxedAutoImplicit = false
linter.style.longLine = true   # Enforce 100 char limit
```

---

## ANTI-PATTERNS ⚠️

### Never Do These

- ❌ **Skip `#lint`** at file end → Always include
- ❌ **Use `sorry` in proofs** → Complete all proofs or mark as TODO
- ❌ **Missing file headers** → Required for all `.lean` files
- ❌ **Implicit instance args** → Always explicit: `[Group G]`
- ❌ **Hardcoded values** → Use named constants
- ❌ **Missing documentation** → Document all public definitions
- ❌ **Mixed import order** → Mathlib first, then local
- ❌ **Commit build artifacts** → `.lake/`, `*.olean` are gitignored

### Code Smells

- Multiple `rw` instead of `simp` with lemmas
- Manual destructuring instead of `obtain` / `rcases`
- Long proof terms instead of `calc` chains
- Missing type annotations on complex definitions

---

## GIT WORKFLOW

### Commit Message Format

Follow `doc/COMMIT_RULES.md`:

```
<type>(<scope>): <subject>

<body>

<footer>
```

**Types:** `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`

**Examples:**
```
feat(Permutation): add phi_mul homomorphism proof

- Prove phi (g₁ * g₂) = phi g₁ * phi g₂
- Use extensionality and calc chains
- Add phi_one identity lemma

Closes #42
```

```
docs(AGENTS): update build commands and style guide
```

### Gitignore

```gitignore
# Build artifacts (DO NOT COMMIT)
.lake/
lake-packages/
build/
*.olean
*.olean.lock

# Editor
.vscode/
.DS_Store

# Dependencies (managed by lake)
Mathlib/
```

---

## QUICK REFERENCE

| Task | Command |
|------|---------|
| Build all | `lake build` |
| Build file | `lake build GroupAction.Defs` |
| Check file | `lake env lean GroupAction/Defs.lean` |
| Clean | `lake clean` |
| Update deps | `lake update` |
| REPL | `lake repl` |
| Lint all | `lake exe lint` |
| Format check | Add `#lint` to file end |

---

## WHERE TO FIND THINGS

| Concept | File | Key Symbols |
|---------|------|-------------|
| Action class | `Defs.lean` | `GroupAction`, `act`, `ga_mul`, `ga_one` |
| Faithful/Transitive | `Defs.lean` | `GroupAction.faithful`, `GroupAction.transitive` |
| Permutation rep | `Permutation.lean` | `sigma`, `sigmaPerm`, `phi`, `phi_apply`, `phi_mul` |
| Stabilizer | `Stabilizer.lean` | `stabilizerSet`, `stabilizer` |
| S₃ action | `Examples.lean` | `s3ActionFin3`, `s3Action_transitive` |
| D₄ action | `Examples.lean` | `d4ActionZMod4`, `d4CenterAction` |

---

## NOTES FOR AI AGENTS

- Always run `lake build` before committing
- push changes to both GitHub and Codeberg
- Check LSP diagnostics in VS Code during development
- Use `#check` and `#print` to explore definitions
- Consult mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- When stuck, search mathlib for similar lemmas with `library_search`
- Coordinate with Orch-GroupAction repository for CI/deployment
