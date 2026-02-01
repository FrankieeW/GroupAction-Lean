# Commit Message Rules

## Format

```
<type>(<scope>): <subject>

<body>

<footer>
```

## Type

| Type | Description |
|------|-------------|
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation only |
| `style` | Formatting, missing semicolons, etc. |
| `refactor` | Code change, no feature/fix |
| `test` | Adding/missing tests |
| `chore` | Maintenance, build scripts |

## Examples

```
feat(auth): add JWT token validation

- Validate token expiration
- Check signature integrity
- Return 401 on invalid tokens

Closes #123
```

```
docs(AGENTS): update commit rules

- Add type table
- Include example
```

## Rules

1. Use imperative mood: "add" not "added"
2. Subject line: 50 chars max
3. Body: 72 chars per line
4. Blank line between body and footer
5. Footer: `Closes #<issue>`, `Fixes #<bug>`
