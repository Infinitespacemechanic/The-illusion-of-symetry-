# The Illusion of Symmetry

> Perfect pairs look like they should cancel into a circle. Lean says they don't.

This repo is two checkable machines, not a poster.

### 1. The stick - `Perfectpairs.lean` / `Reverse-for-unstable-map.lean`

`stepU`:
- even → n+3
- odd → n+1

Two steps always = +4. Unique predecessor, inverse exists.

After k double-steps: n + 4k. For k≠0, never n.

Lean: orbit is an open line. A stick. Not a circle.

### 2. The shadow - why it *looks* like a circle

n : ℤ is the one additive thing. It has two shadows, both additive homomorphisms:

```lean
def residue (n : ℤ) : ZMod 720 := (n : ZMod 720)
def radian (n : ℝ) : ℝ := n * (Real.pi / 360)
```

- residue = what the circle sees mod 720
- radian = what angle sees mod 2π

Same +4k in both:

```
residue (n + 4k) = residue n + 4k  (mod 720)
radian (4k) = k * (π / 90)
```

At k=180:
- residue: n+720 = n  → looks closed
- radian: 720 * π/360 = 2π → full turn, looks closed
- ℤ: n+720 ≠ n → still open

720 = 2×360 is degree count on S¹. 6! too. The +4 walk only sees residue class mod 4 unless you project it. The illusion is the projection.

### 3. Why this matters for NS - forced vs unforced

From discussion with OpenAI (Gonzalo Cao-Labora thread):

Clay NS has 4 statements:
- A: R³, unforced → stays smooth? (yes)
- B: T³ torus, unforced → stays smooth? (yes)
- C: R³, forced with smooth f → can break? (no to smoothness)
- D: T³, forced → can break? (no)

All 4 can be true at once: left alone water never kinks (A/B true), but if you keep pushing the right way you can make it blow up (C/D true).

Mapping to this repo / vortex cannon:
- f = rotors, prop, piston, rim jet (τ ~ ṁ v_jet R)
- f=0 = remove prop, only water on water + viscosity
- container / lip / hole = boundary conditions (R³ vs T³)

OpenAI's construction is forced blow-up (f ≠ 0, C/D territory). Constantin-Ignatova-Vicol says that shape cannot have real-analytic f, and in particular cannot have f=0. Removing force is not a small mod - it's a different theorem.

The ball in water:
Low Ω → clean torus, predictable. Mid Ω → one stable ring ("right speed"). High Ω → tangle / turbulence, Re_Ω = ΩR²/ν = ρΩR²/μ. Cut supply → f=0, spin decays.

Same lesson as stick vs shadow:
- residue / radian = what you see while pushing
- ℤ = what remains after push stops

### 4. Earth is a lot of atoms

Gravity:
- Specific weight γ = ρg, γ_water ≈ 9810 N/m³
- g(r) = GM/r², external field
- GR: G_μν + Λg_μν = (8πG/c⁴) T_μν

In c=1 units, E = mc² → E = M (rest energy). Full source is T_μν: energy density, momentum, pressure, stress.

Chain:
atoms → mass-energy (E=M when c=1) → T_μν → curvature → motion + pressure gradient dp/dz = -ρg

No Earth mass, no Earth field. Specific weight is response, not source.

### Build

```bash
lake build Perfectpairs
lake build Reverse-for-unstable-map
```

Both should complete. The slogan is now Lean-checkable: shadows close, stick stays open.
