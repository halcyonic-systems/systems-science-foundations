@AGENTS.md

## Claude Code only

- In the Halcyonic setup, a build-check hook runs `lake build` after `.lean`
  edits and scans the output for transitive `sorry` as a zero-sorry guard.
- Explore and Plan subagents skip this file and its import. When delegating,
  put claim hygiene (no free-category maximality) and zero-`sorry` in the prompt.
- Subagents that edit this repo use `isolation: worktree`.
