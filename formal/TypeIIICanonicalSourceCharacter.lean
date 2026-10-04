import TypeIIICanonicalCoefficients
import TypeIIIKatzSourceNormalization

/-!
# The published source character and the exact finite-field character

Use the fixed two-adic coefficient field and complex embedding already
selected by the source construction. Pulling back the standard character
through that embedding gives the nontrivial character used by the published
AS and Kloosterman theorems. Extension uses the actual field trace, including
extensions whose degree is divisible by p. No character sheaf is constructed
or its published trace theorem proved in this module.
-/

noncomputable section
open scoped PrimeGap182.TypeIII.TwoAdicComplexEmbedding

namespace PrimeGap182.TypeIII.CanonicalSourceCharacter

open TwoAdicComplexEmbedding

variable (p : ℕ) [Fact p.Prime]

def prime : AddChar (ZMod p) (PadicAlgCl 2) :=
  complexEquiv.symm.toMonoidHom.compAddChar (ZMod.stdAddChar (N := p))

theorem prime_complex (t : ZMod p) :
    complexEquiv (prime p t) = ZMod.stdAddChar t :=
  complexEquiv.apply_symm_apply _

theorem prime_one : prime p 1 = CanonicalCoefficients.zeta p := rfl

theorem prime_ne_one : prime p ≠ 1 := by
  intro h
  have he := congrArg complexEquiv (DFunLike.congr_fun h (1 : ZMod p))
  rw [prime_complex] at he
  have hz : ZMod.stdAddChar (1 : ZMod p) = ZMod.stdAddChar (0 : ZMod p) := by
    simpa using he
  exact one_ne_zero (ZMod.injective_stdAddChar hz)

variable (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]

def extension : AddChar E (PadicAlgCl 2) :=
  (prime p).compAddMonoidHom (Algebra.trace (ZMod p) E).toAddMonoidHom

omit [Fintype E] in
theorem extension_complex (z : E) :
    complexEquiv (extension p E z) = FiniteFieldSums.traceAddChar p E z :=
  prime_complex p _

theorem extension_ne_one : extension p E ≠ 1 := by
  intro h
  apply FiniteFieldSums.traceAddChar_ne_one p E
  apply AddChar.ext
  intro z
  have he := congrArg complexEquiv (DFunLike.congr_fun h z)
  rw [extension_complex] at he
  simpa using he

theorem prime_action (hp : 3 < p) (t : ZMod p) :
    CanonicalCoefficients.tau p hp (prime p t) = prime p (2 * t) := by
  apply complexEquiv.injective
  change algebraMap (PadicAlgCl 2) ℂ
    (CanonicalCoefficients.tau p hp (prime p t)) = _
  rw [← CanonicalCoefficients.sigma_on_coefficients]
  change CanonicalCoefficients.sigma p hp (complexEquiv (prime p t)) = _
  rw [prime_complex, CanonicalCoefficients.sigma_stdAddChar, prime_complex]

end PrimeGap182.TypeIII.CanonicalSourceCharacter

#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.prime_complex
#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.prime_one
#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.prime_ne_one
#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.extension_complex
#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.extension_ne_one
#print axioms PrimeGap182.TypeIII.CanonicalSourceCharacter.prime_action
