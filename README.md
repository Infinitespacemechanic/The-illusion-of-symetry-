# The Illusion of Symmetry

> We love dual hemispheres... 720... two 360's... perfect pairs... cancel, dampen... spin out!

This repo is about the illusion that symmetry closes.

At a distance a path looks like a circle. Zoom in, it's a perfect square. Zoom out, it's a stick - an open line that never returns.

### The core idea

Two hemispheres = `720 = 2 * 360`. Two perfect pairs that look like they should cancel to a circle, but don't.

The mechanic picture:
* **perfect square** = `4 = 2²` - the scarce unit
* **circle** = many squares stitched - looks closed
* **stick** = the same thread followed forward or backward - open

### The checkable half - stepU (standalone)

No `stepS` needed for this.

```lean
def stepU (n : ℤ) : ℤ := if Even n then n + 3 else n + 1
def stepU_inv (m : ℤ) : ℤ := if Even m then m - 1 else m - 3
```

* forward 2 steps: `stepU (stepU n) = n + 4`
* backward 2 steps: `stepU_inv (stepU_inv m) = m - 4`
* unique predecessor: `even m` came from `m-1`, `odd m` came from `m-3`
* thread can be followed either way and never closes: `4*k ≠ 0` for `k ≠ 0`

This is the lean, efficient scaling - linear `+4*k`, not tetration like Graham's number, not exponential like Euler scaling. It goes far by compounding naturally.

### Files

* `Perfectpairs.lean` - the standalone Lean proof. No axioms beyond `Mathlib.Data.Int.ModEq`. Builds green with `lake build`.
* `stepU` + `stepU_inv` is the open line. The prime-sphere picture is a comment, not a definition.

### Why it matters

Perfect pairs *look* like they cancel, dampen, spin out to a circle. Lean says: they don't. The thread stays open.

```
square -> circle -> stick
```

Follow it up to go down. Same game Euler played, but cleaner.
