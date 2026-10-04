import TypeIIIFullFourierKernelCoordinates

/-!
# The actual positive rank-two Fourier kernel coordinates

The full affine four-space has source x0,x1 and target y0,y1 coordinates.
Both source and target origins are retained. Projection maps and the
positive pairing x0*y0+x1*y1 are actual affine scheme morphisms. Reflection
on the full affine plane is the involution x -> -x, including its origin.
Only polynomial and affine scheme identities are constructed here.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates

universe u
variable (k : Type u) [Field k]

abbrev KernelRing := MvPolynomial (Fin 4) k
abbrev kernelScheme : Scheme := Spec (.of (KernelRing k))
abbrev planeScheme : Scheme := FullFourierKernelCoordinates.planeScheme k
abbrev lineScheme : Scheme := LocalFourierKernelCoordinates.affineLine k

/-- Projection retains the literal first two source coordinates. -/
def sourceHom : MvPolynomial (Fin 2) k →ₐ[k] KernelRing k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (Fin.castAdd 2 i))

/-- Projection retains the literal last two target coordinates. -/
def targetHom : MvPolynomial (Fin 2) k →ₐ[k] KernelRing k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (Fin.natAdd 2 i))

/-- The positive dot-product kernel on the full affine four-space. -/
def pairingHom : MvPolynomial (Fin 1) k →ₐ[k] KernelRing k :=
  MvPolynomial.aeval (fun _ =>
    MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 3)

/-- Negate every plane coordinate, with the same coefficient field. -/
def reflectionHom : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (fun i => -MvPolynomial.X i)

@[simp] theorem sourceHom_X (i : Fin 2) :
    sourceHom k (MvPolynomial.X i) = MvPolynomial.X (Fin.castAdd 2 i) :=
  MvPolynomial.aeval_X _ _

@[simp] theorem targetHom_X (i : Fin 2) :
    targetHom k (MvPolynomial.X i) = MvPolynomial.X (Fin.natAdd 2 i) :=
  MvPolynomial.aeval_X _ _

@[simp] theorem pairingHom_X (i : Fin 1) :
    pairingHom k (MvPolynomial.X i) =
      MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 3 :=
  MvPolynomial.aeval_X _ _

@[simp] theorem reflectionHom_X (i : Fin 2) :
    reflectionHom k (MvPolynomial.X i) = -MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

/-- Reflection is an actual involution of the coordinate algebra. -/
theorem reflectionHom_square : (reflectionHom k).comp (reflectionHom k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- Reflection is also an involution as a ring homomorphism. -/
theorem reflectionRingHom_square :
    (reflectionHom k).toRingHom.comp (reflectionHom k).toRingHom = RingHom.id _ :=
  congrArg AlgHom.toRingHom (reflectionHom_square k)

def sourceMorphism : kernelScheme k ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (sourceHom k).toRingHom)

def targetMorphism : kernelScheme k ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (targetHom k).toRingHom)

def pairingMorphism : kernelScheme k ⟶ lineScheme k :=
  Spec.map (CommRingCat.ofHom (pairingHom k).toRingHom)

def reflectionMorphism : planeScheme k ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (reflectionHom k).toRingHom)

/-- Scheme reflection squared is the identity on the FULL plane. -/
theorem reflectionMorphism_square : reflectionMorphism k ≫ reflectionMorphism k = 𝟙 _ := by
  dsimp only [reflectionMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, reflectionRingHom_square]
  exact Spec.map_id _

/-- The actual full-plane reflection isomorphism. -/
def reflectionIso : planeScheme k ≅ planeScheme k where
  hom := reflectionMorphism k
  inv := reflectionMorphism k
  hom_inv_id := reflectionMorphism_square k
  inv_hom_id := reflectionMorphism_square k

/-- Evaluation of the positive kernel at arbitrary field coordinates. -/
theorem pairing_value (v : Fin 4 → k) :
    MvPolynomial.eval v (pairingHom k (MvPolynomial.X 0)) = v 0 * v 2 + v 1 * v 3 := by
  simp

/-- The kernel vanishes along the ENTIRE source-origin plane, including
both target-zero and target-nonzero points. -/
theorem pairing_at_source_origin (v : Fin 4 → k) (h0 : v 0 = 0) (h1 : v 1 = 0) :
    MvPolynomial.eval v (pairingHom k (MvPolynomial.X 0)) = 0 := by
  rw [pairing_value, h0, h1]
  simp

/-- The kernel vanishes along the ENTIRE target-origin plane. -/
theorem pairing_at_target_origin (v : Fin 4 → k) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    MvPolynomial.eval v (pairingHom k (MvPolynomial.X 0)) = 0 := by
  rw [pairing_value, h2, h3]
  simp

/-- Literal rational affine points, with no removal of any coordinate origin. -/
def kernelPoint (v : Fin 4 → k) : Spec (.of k) ⟶ kernelScheme k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval v))

def planePoint (v : Fin 2 → k) : Spec (.of k) ⟶ planeScheme k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval v))

def linePoint (a : k) : Spec (.of k) ⟶ lineScheme k :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ => a)))

/-- Coordinate evaluation and projection commute as ring maps. -/
theorem source_evaluation (v : Fin 4 → k) :
    (MvPolynomial.eval v).comp (sourceHom k).toRingHom =
      MvPolynomial.eval (fun i => v (Fin.castAdd 2 i)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [sourceHom]
  · intro i
    simp

theorem target_evaluation (v : Fin 4 → k) :
    (MvPolynomial.eval v).comp (targetHom k).toRingHom =
      MvPolynomial.eval (fun i => v (Fin.natAdd 2 i)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [targetHom]
  · intro i
    simp

theorem pairing_evaluation (v : Fin 4 → k) :
    (MvPolynomial.eval v).comp (pairingHom k).toRingHom =
      MvPolynomial.eval (fun _ => v 0 * v 2 + v 1 * v 3) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [pairingHom]
  · intro i
    simp

theorem reflection_evaluation (v : Fin 2 → k) :
    (MvPolynomial.eval v).comp (reflectionHom k).toRingHom = MvPolynomial.eval (fun i => -v i) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [reflectionHom]
  · intro i
    simp

/-- Actual affine source projection at every rational point. -/
theorem kernelPoint_source (v : Fin 4 → k) :
    kernelPoint k v ≫ sourceMorphism k = planePoint k (fun i => v (Fin.castAdd 2 i)) := by
  dsimp only [kernelPoint, sourceMorphism, planePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, source_evaluation]

/-- Actual affine target projection at every rational point. -/
theorem kernelPoint_target (v : Fin 4 → k) :
    kernelPoint k v ≫ targetMorphism k = planePoint k (fun i => v (Fin.natAdd 2 i)) := by
  dsimp only [kernelPoint, targetMorphism, planePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, target_evaluation]

theorem kernelPoint_pairing (v : Fin 4 → k) :
    kernelPoint k v ≫ pairingMorphism k = linePoint k (v 0 * v 2 + v 1 * v 3) := by
  dsimp only [kernelPoint, pairingMorphism, linePoint]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, pairing_evaluation]

/-- Reflection fixes the actual affine origin and negates all points. -/
theorem planePoint_reflection (v : Fin 2 → k) :
    planePoint k v ≫ reflectionMorphism k = planePoint k (fun i => -v i) := by
  dsimp only [planePoint, reflectionMorphism]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, reflection_evaluation]

theorem plane_origin_reflection :
    planePoint k (fun _ => 0) ≫ reflectionMorphism k = planePoint k (fun _ => 0) := by
  simpa only [neg_zero] using planePoint_reflection k (fun _ => 0)

theorem full_origin_source :
    kernelPoint k (fun _ => 0) ≫ sourceMorphism k = planePoint k (fun _ => 0) :=
  kernelPoint_source k (fun _ => 0)

theorem full_origin_target :
    kernelPoint k (fun _ => 0) ≫ targetMorphism k = planePoint k (fun _ => 0) :=
  kernelPoint_target k (fun _ => 0)

theorem full_origin_pairing :
    kernelPoint k (fun _ => 0) ≫ pairingMorphism k = linePoint k 0 := by
  simpa only [mul_zero, zero_add] using kernelPoint_pairing k (fun _ => 0)

end PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates

#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.reflectionRingHom_square
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.reflectionMorphism_square
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.reflectionIso
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.pairing_at_source_origin
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.pairing_at_target_origin
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.kernelPoint_source
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.kernelPoint_target
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.kernelPoint_pairing
#print axioms PrimeGap182.TypeIII.RankTwoFourierKernelCoordinates.plane_origin_reflection
