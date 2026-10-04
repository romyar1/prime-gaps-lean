import TypeIIILinearFourierTransposeCoordinates
import TypeIIINativeSurfaceFromGeometricStalks

/-!
# Rational image of the actual coefficient-line transpose

The image uses the SAME native geometric point maps used for surface
stalks. It is proved to be the original homogeneous support line from
the checked polynomial/Spec coordinate identities, with no sheaf or
support theorem as an input.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.LinearFourierRationalImage
open LinearFourierTransposeCoordinates

variable (k : Type) [Field k]

/-- ACTUAL rational-point image, using the native surface point maps. -/
def rationalImage (f : lineScheme k ⟶ planeScheme k) : Set (k × k) :=
  {z | ∃ t, NativeSurfaceFromGeometricStalks.linePointMorphism k t ≫ f =
    NativeSurfaceFromGeometricStalks.pointMorphism k z}

theorem native_linePoint (t : k) :
    NativeSurfaceFromGeometricStalks.linePointMorphism k t =
      RankTwoFourierKernelCoordinates.linePoint k t := rfl

theorem native_planePoint (z : k × k) :
    NativeSurfaceFromGeometricStalks.pointMorphism k z =
      RankTwoFourierKernelCoordinates.planePoint k ![z.1, z.2] := rfl

/-- Transpose evaluated at EVERY native rational point. -/
theorem point_transposeMorphism (a b t : k) :
    NativeSurfaceFromGeometricStalks.linePointMorphism k t ≫ transposeMorphism k a b =
      NativeSurfaceFromGeometricStalks.pointMorphism k (a * t, b * t) :=
  LinearFourierTransposeCoordinates.point_transposeMorphism k a b t

/-- The ACTUAL image is exactly the coefficient line, including its origin. -/
theorem rationalImage_transpose (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    rationalImage k (transposeMorphism k a b) = ScalingLines.originLine (-b) a := by
  ext z
  exact point_factors_iff k a b hab z

/-- EXACT old inverse_line_pullback sign convention on the same native points. -/
theorem rationalImage_transpose_rotated (a b : k) (hab : a ≠ 0 ∨ b ≠ 0) :
    rationalImage k (transposeMorphism k b (-a)) = ScalingLines.originLine a b := by
  ext z
  exact normal_point_factors_iff k a b hab z

end PrimeGap182.TypeIII.LinearFourierRationalImage

#print axioms PrimeGap182.TypeIII.LinearFourierRationalImage.rationalImage_transpose
#print axioms PrimeGap182.TypeIII.LinearFourierRationalImage.rationalImage_transpose_rotated
