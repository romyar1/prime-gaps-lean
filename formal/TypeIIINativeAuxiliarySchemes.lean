import TypeIIIRadialGenericDominance
import TypeIIINativeSurfaceFromGeometricStalks
import TypeIIIRankTwoFourierKernelCoordinates
import TypeIIIUniformComplexityFromCommonRealization

/-!
# Fixed auxiliary schemes in the one ordinary inverse-image extension

The arithmetic QST plane over K0, geometric point over k, and full
rank-two Fourier product over k and the literal radial generic field spectrum
are DISTINCT slots. The native curve,
native plane, origin trait and punctured trait retain their existing
OriginPole slots. No category, inverse image or geometric theorem is
chosen by this finite scheme inventory.
-/

noncomputable section
open AlgebraicGeometry

namespace PrimeGap182.TypeIII.NativeAuxiliarySchemes

inductive Space
  | arithmeticPlane
  | geometricPoint
  | fourierProduct
  | radialGeneric

variable (K0 k : Type) [Field K0] [Field k]

def scheme : Space → Scheme
  | .arithmeticPlane => UniformComplexityFromCommonRealization.affinePlane K0
  | .geometricPoint => NativeSurfaceFromGeometricStalks.pointScheme k
  | .fourierProduct => RankTwoFourierKernelCoordinates.kernelScheme k
  | .radialGeneric => RadialGenericDominance.genericScheme k

end PrimeGap182.TypeIII.NativeAuxiliarySchemes

