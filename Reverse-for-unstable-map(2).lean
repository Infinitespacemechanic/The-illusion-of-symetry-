import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds

def residue (n : ℤ) : ZMod 720 := (n : ZMod 720)
def radian (n : ℝ) : ℝ := n * (Real.pi / 360)

-- residue is additive homomorphism ℤ → ZMod 720
theorem residue_add (a b : ℤ) : residue (a + b) = residue a + residue b := by
  unfold residue; push_cast; rfl

-- radian is additive / linear in ℝ
theorem radian_add (a b : ℝ) : radian (a + b) = radian a + radian b := by
  unfold radian; ring

theorem radian_mul (k : ℕ) : radian (4 * k : ℝ) = k * (Real.pi / 90) := by
  unfold radian; ring

-- the bridge: same +4k seen in both shadows
theorem bridge (n : ℤ) (k : ℕ) :
  residue (n + 4 * k) = residue n + (4 * k : ZMod 720) ∧
  radian (4 * k : ℝ) = (k : ℝ) * (Real.pi / 90) := by
  constructor
  · unfold residue; push_cast; rfl
  · unfold radian; ring

-- the illusion at k=180: residue says 0, radian says 2π, ℤ says +720 ≠ 0
theorem illusion_720 (n : ℤ) : residue (n + 720) = residue n := by
  have : (720 : ZMod 720) = 0 := by decide
  calc residue (n + 720) = residue n + (720 : ZMod 720) := by
        unfold residue; push_cast; rfl
    _ = residue n + 0 := by rw [this]
    _ = residue n := by ring

theorem radian_720 : radian (720 : ℝ) = 2 * Real.pi := by
  unfold radian; ring